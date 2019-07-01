/**
 *  @file
 *  @copyright defined in eos/LICENSE.txt
 *
 */
#include <eosio.system/eosio.system.hpp>

#include <eosiolib/eosio.hpp>
#include <eosiolib/print.hpp>
#include <eosiolib/datastream.hpp>
#include <eosiolib/serialize.hpp>
#include <eosiolib/multi_index.hpp>
#include <eosiolib/privileged.h>
#include <eosiolib/transaction.hpp>

#include <eosio.token/eosio.token.hpp>

#include <cmath>
#include <map>
#include <algorithm>

namespace eosiosystem {
   using eosio::asset;
   using eosio::indexed_by;
   using eosio::const_mem_fun;
   using eosio::print;
   using eosio::permission_level;
   using eosio::time_point_sec;
   using eosio::time_point;
   using std::map;
   using std::pair;

   static constexpr uint32_t refund_delay_sec = 3*24*3600;
   static constexpr int64_t  ram_gift_bytes = 1400;

   struct [[eosio::table, eosio::contract("eosio.system")]] user_resources {
      name          owner;
      asset         net_weight;
      asset         cpu_weight;
      int64_t       ram_bytes = 0;

      uint64_t primary_key()const { return owner.value; }

      // explicit serialization macro is not necessary, used here only to improve compilation time
      EOSLIB_SERIALIZE( user_resources, (owner)(net_weight)(cpu_weight)(ram_bytes) )
   };


   /**
    *  Every user 'from' has a scope/table that uses every receipient 'to' as the primary key.
    */
   struct [[eosio::table, eosio::contract("eosio.system")]] delegated_bandwidth {
      name          from;
      name          to;
      asset         net_weight;
      asset         cpu_weight;

      uint64_t  primary_key()const { return to.value; }

      // explicit serialization macro is not necessary, used here only to improve compilation time
      EOSLIB_SERIALIZE( delegated_bandwidth, (from)(to)(net_weight)(cpu_weight) )

   };

   struct [[eosio::table, eosio::contract("eosio.system")]] refund_request {
      name            owner;
      time_point_sec  request_time;
      eosio::asset    net_amount;
      eosio::asset    cpu_amount;

      uint64_t  primary_key()const { return owner.value; }

      // explicit serialization macro is not necessary, used here only to improve compilation time
      EOSLIB_SERIALIZE( refund_request, (owner)(request_time)(net_amount)(cpu_amount) )
   };

   struct [[eosio::table, eosio::contract("eosio.system")]] genesis_nonce {
      uint64_t       nonce;
      eosio::asset   awarded;
      name           receiver;

      uint64_t primary_key() const { return nonce; }

      // explicit serialization macro is not necessary, used here only to improve compilation time
      EOSLIB_SERIALIZE(genesis_nonce, (nonce)(awarded)(receiver))
   };

   struct [[eosio::table, eosio::contract("eosio.system")]] genesis_tokens {
      eosio::asset    balance;
      eosio::asset    unclaimed_balance;
      time_point      last_claim_time;
      time_point      last_updated;

      uint64_t primary_key()const { return balance.symbol.code().raw(); }

      // explicit serialization macro is not necessary, used here only to improve compilation time
      EOSLIB_SERIALIZE( genesis_tokens,(balance)(unclaimed_balance)(last_claim_time)(last_updated) )
   };

   /**
    *  These tables are designed to be constructed in the scope of the relevant user, this
    *  facilitates simpler API for per-user queries
    */
   typedef eosio::multi_index< "userres"_n, user_resources >      user_resources_table;
   typedef eosio::multi_index< "delband"_n, delegated_bandwidth > del_bandwidth_table;
   typedef eosio::multi_index< "refunds"_n, refund_request >      refunds_table;
   typedef eosio::multi_index< "genesis"_n, genesis_tokens >      genesis_balance_table;
   typedef eosio::multi_index< "genonce"_n, genesis_nonce >       genesis_nonce_table;



   /**
    *  This action will buy an exact amount of ram and bill the payer the current market price.
    */
   void system_contract::buyrambytes( name payer, name receiver, uint32_t bytes ) {

      auto itr = _rammarket.find(ramcore_symbol.raw());
      auto tmp = *itr;
      auto eosout = tmp.convert( asset(bytes, ram_symbol), core_symbol() );

      buyram( payer, receiver, eosout );
   }


   /**
    *  When buying ram the payer irreversiblly transfers quant to system contract and only
    *  the receiver may reclaim the tokens via the sellram action. The receiver pays for the
    *  storage of all database records associated with this action.
    *
    *  RAM is a scarce resource whose supply is defined by global properties max_ram_size. RAM is
    *  priced using the bancor algorithm such that price-per-byte with a constant reserve ratio of 100:1.
    */
   void system_contract::buyram( name payer, name receiver, asset quant )
   {
      require_auth( payer );
      update_ram_supply();

      eosio_assert( quant.symbol == core_symbol(), "must buy ram with core token" );
      eosio_assert( quant.amount > 0, "must purchase a positive amount" );

      auto fee = quant;
      fee.amount = ( fee.amount + 199 ) / 200; /// .5% fee (round up)
      // fee.amount cannot be 0 since that is only possible if quant.amount is 0 which is not allowed by the assert above.
      // If quant.amount == 1, then fee.amount == 1,
      // otherwise if quant.amount > 1, then 0 < fee.amount < quant.amount.
      auto quant_after_fee = quant;
      quant_after_fee.amount -= fee.amount;
      // quant_after_fee.amount should be > 0 if quant.amount > 1.
      // If quant.amount == 1, then quant_after_fee.amount == 0 and the next inline transfer will fail causing the buyram action to fail.

      INLINE_ACTION_SENDER(eosio::token, transfer)(
         token_account, { {payer, active_permission}, {ram_account, active_permission} },
         { payer, ram_account, quant_after_fee, std::string("buy ram") }
      );

      if( fee.amount > 0 ) {
         INLINE_ACTION_SENDER(eosio::token, transfer)(
            token_account, { {payer, active_permission} },
            { payer, ramfee_account, fee, std::string("ram fee") }
         );
      }

      int64_t bytes_out;

      const auto& market = _rammarket.get(ramcore_symbol.raw(), "ram market does not exist");
      _rammarket.modify( market, same_payer, [&]( auto& es ) {
          bytes_out = es.convert( quant_after_fee,  ram_symbol ).amount;
      });

      eosio_assert( bytes_out > 0, "must reserve a positive amount" );

      _gstate.total_ram_bytes_reserved += uint64_t(bytes_out);
      _gstate.total_ram_stake          += quant_after_fee.amount;

      user_resources_table  userres( _self, receiver.value );
      auto res_itr = userres.find( receiver.value );
      if( res_itr ==  userres.end() ) {
         res_itr = userres.emplace( receiver, [&]( auto& res ) {
               res.owner = receiver;
               res.net_weight = asset( 0, core_symbol() );
               res.cpu_weight = asset( 0, core_symbol() );
               res.ram_bytes = bytes_out;
            });
      } else {
         userres.modify( res_itr, receiver, [&]( auto& res ) {
               res.ram_bytes += bytes_out;
            });
      }

      auto voter_itr = _voters.find( res_itr->owner.value );
      if( voter_itr == _voters.end() || !has_field( voter_itr->flags1, voter_info::flags1_fields::ram_managed ) ) {
         int64_t ram_bytes, net, cpu;
         get_resource_limits( res_itr->owner.value, &ram_bytes, &net, &cpu );
         set_resource_limits( res_itr->owner.value, res_itr->ram_bytes + ram_gift_bytes, net, cpu );
      }
   }

  /**
    *  The system contract now buys and sells RAM allocations at prevailing market prices.
    *  This may result in traders buying RAM today in anticipation of potential shortages
    *  tomorrow. Overall this will result in the market balancing the supply and demand
    *  for RAM over time.
    */
   void system_contract::sellram( name account, int64_t bytes ) {
      require_auth( account );
      update_ram_supply();

      eosio_assert( bytes > 0, "cannot sell negative byte" );

      user_resources_table  userres( _self, account.value );
      auto res_itr = userres.find( account.value );
      eosio_assert( res_itr != userres.end(), "no resource row" );
      eosio_assert( res_itr->ram_bytes >= bytes, "insufficient quota" );

      asset tokens_out;
      auto itr = _rammarket.find(ramcore_symbol.raw());
      _rammarket.modify( itr, same_payer, [&]( auto& es ) {
          /// the cast to int64_t of bytes is safe because we certify bytes is <= quota which is limited by prior purchases
          tokens_out = es.convert( asset(bytes, ram_symbol), core_symbol());
      });

      eosio_assert( tokens_out.amount > 1, "token amount received from selling ram is too low" );

      _gstate.total_ram_bytes_reserved -= static_cast<decltype(_gstate.total_ram_bytes_reserved)>(bytes); // bytes > 0 is asserted above
      _gstate.total_ram_stake          -= tokens_out.amount;

      //// this shouldn't happen, but just in case it does we should prevent it
      eosio_assert( _gstate.total_ram_stake >= 0, "error, attempt to unstake more tokens than previously staked" );

      userres.modify( res_itr, account, [&]( auto& res ) {
          res.ram_bytes -= bytes;
      });

      auto voter_itr = _voters.find( res_itr->owner.value );
      if( voter_itr == _voters.end() || !has_field( voter_itr->flags1, voter_info::flags1_fields::ram_managed ) ) {
         int64_t ram_bytes, net, cpu;
         get_resource_limits( res_itr->owner.value, &ram_bytes, &net, &cpu );
         set_resource_limits( res_itr->owner.value, res_itr->ram_bytes + ram_gift_bytes, net, cpu );
      }

      INLINE_ACTION_SENDER(eosio::token, transfer)(
         token_account, { {ram_account, active_permission}, {account, active_permission} },
         { ram_account, account, asset(tokens_out), std::string("sell ram") }
      );

      auto fee = ( tokens_out.amount + 199 ) / 200; /// .5% fee (round up)
      // since tokens_out.amount was asserted to be at least 2 earlier, fee.amount < tokens_out.amount
      if( fee > 0 ) {
         INLINE_ACTION_SENDER(eosio::token, transfer)(
            token_account, { {account, active_permission} },
            { account, ramfee_account, asset(fee, core_symbol()), std::string("sell ram fee") }
         );
      }
   }

   void validate_b1_vesting( int64_t stake ) {
      const int64_t base_time = 1527811200; /// 2018-06-01
      const int64_t max_claimable = 100'000'000'0000ll;
      const int64_t claimable = int64_t(max_claimable * double(now()-base_time) / (10*seconds_per_year) );

      eosio_assert( max_claimable - claimable <= stake, "b1 can only claim their tokens over 10 years" );
   }

   void system_contract::changebw( name from, name receiver,
                                   const asset stake_net_delta, const asset stake_cpu_delta, bool transfer )
   {
      require_auth( from );
      eosio_assert( stake_net_delta.amount != 0 || stake_cpu_delta.amount != 0, "should stake non-zero amount" );
      eosio_assert( std::abs( (stake_net_delta + stake_cpu_delta).amount )
                     >= std::max( std::abs( stake_net_delta.amount ), std::abs( stake_cpu_delta.amount ) ),
                    "net and cpu deltas cannot be opposite signs" );

      name source_stake_from = from;
      if ( transfer ) {
         from = receiver;
      }

      // update stake delegated from "from" to "receiver"
      {
         del_bandwidth_table     del_tbl( _self, from.value );
         auto itr = del_tbl.find( receiver.value );
         if( itr == del_tbl.end() ) {
            itr = del_tbl.emplace( from, [&]( auto& dbo ){
                  dbo.from          = from;
                  dbo.to            = receiver;
                  dbo.net_weight    = stake_net_delta;
                  dbo.cpu_weight    = stake_cpu_delta;
               });
         }
         else {
            del_tbl.modify( itr, same_payer, [&]( auto& dbo ){
                  dbo.net_weight    += stake_net_delta;
                  dbo.cpu_weight    += stake_cpu_delta;
               });
         }
         eosio_assert( 0 <= itr->net_weight.amount, "insufficient staked net bandwidth" );
         eosio_assert( 0 <= itr->cpu_weight.amount, "insufficient staked cpu bandwidth" );
         if ( itr->net_weight.amount == 0 && itr->cpu_weight.amount == 0 ) {
            del_tbl.erase( itr );
         }
      } // itr can be invalid, should go out of scope

      // update totals of "receiver"
      {
         user_resources_table   totals_tbl( _self, receiver.value );
         auto tot_itr = totals_tbl.find( receiver.value );
         if( tot_itr ==  totals_tbl.end() ) {
            tot_itr = totals_tbl.emplace( from, [&]( auto& tot ) {
                  tot.owner = receiver;
                  tot.net_weight    = stake_net_delta;
                  tot.cpu_weight    = stake_cpu_delta;
               });
         } else {
            totals_tbl.modify( tot_itr, from == receiver ? from : same_payer, [&]( auto& tot ) {
                  tot.net_weight    += stake_net_delta;
                  tot.cpu_weight    += stake_cpu_delta;
               });
         }
         eosio_assert( 0 <= tot_itr->net_weight.amount, "insufficient staked total net bandwidth" );
         eosio_assert( 0 <= tot_itr->cpu_weight.amount, "insufficient staked total cpu bandwidth" );

         {
            bool ram_managed = false;
            bool net_managed = false;
            bool cpu_managed = false;

            auto voter_itr = _voters.find( receiver.value );
            if( voter_itr != _voters.end() ) {
               ram_managed = has_field( voter_itr->flags1, voter_info::flags1_fields::ram_managed );
               net_managed = has_field( voter_itr->flags1, voter_info::flags1_fields::net_managed );
               cpu_managed = has_field( voter_itr->flags1, voter_info::flags1_fields::cpu_managed );
            }

            if( !(net_managed && cpu_managed) ) {
               int64_t ram_bytes, net, cpu;
               get_resource_limits( receiver.value, &ram_bytes, &net, &cpu );

               set_resource_limits( receiver.value,
                                    ram_managed ? ram_bytes : std::max( tot_itr->ram_bytes + ram_gift_bytes, ram_bytes ),
                                    net_managed ? net : tot_itr->net_weight.amount,
                                    cpu_managed ? cpu : tot_itr->cpu_weight.amount );
            }
         }

         if ( tot_itr->net_weight.amount == 0 && tot_itr->cpu_weight.amount == 0  && tot_itr->ram_bytes == 0 ) {
            totals_tbl.erase( tot_itr );
         }
      } // tot_itr can be invalid, should go out of scope

      // create refund or update from existing refund
      if ( stake_account != source_stake_from ) { //for eosio both transfer and refund make no sense
         refunds_table refunds_tbl( _self, from.value );
         auto req = refunds_tbl.find( from.value );

         //create/update/delete refund
         auto net_balance = stake_net_delta;
         auto cpu_balance = stake_cpu_delta;
         bool need_deferred_trx = false;


         // net and cpu are same sign by assertions in delegatebw and undelegatebw
         // redundant assertion also at start of changebw to protect against misuse of changebw
         bool is_undelegating = (net_balance.amount + cpu_balance.amount ) < 0;
         bool is_delegating_to_self = (!transfer && from == receiver);

         if( is_delegating_to_self || is_undelegating ) {
            if ( req != refunds_tbl.end() ) { //need to update refund
               refunds_tbl.modify( req, same_payer, [&]( refund_request& r ) {
                  if ( net_balance.amount < 0 || cpu_balance.amount < 0 ) {
                     r.request_time = current_time_point();
                  }
                  r.net_amount -= net_balance;
                  if ( r.net_amount.amount < 0 ) {
                     net_balance = -r.net_amount;
                     r.net_amount.amount = 0;
                  } else {
                     net_balance.amount = 0;
                  }
                  r.cpu_amount -= cpu_balance;
                  if ( r.cpu_amount.amount < 0 ){
                     cpu_balance = -r.cpu_amount;
                     r.cpu_amount.amount = 0;
                  } else {
                     cpu_balance.amount = 0;
                  }
               });

               eosio_assert( 0 <= req->net_amount.amount, "negative net refund amount" ); //should never happen
               eosio_assert( 0 <= req->cpu_amount.amount, "negative cpu refund amount" ); //should never happen

               if ( req->net_amount.amount == 0 && req->cpu_amount.amount == 0 ) {
                  refunds_tbl.erase( req );
                  need_deferred_trx = false;
               } else {
                  need_deferred_trx = true;
               }
            } else if ( net_balance.amount < 0 || cpu_balance.amount < 0 ) { //need to create refund
               refunds_tbl.emplace( from, [&]( refund_request& r ) {
                  r.owner = from;
                  if ( net_balance.amount < 0 ) {
                     r.net_amount = -net_balance;
                     net_balance.amount = 0;
                  } else {
                     r.net_amount = asset( 0, core_symbol() );
                  }
                  if ( cpu_balance.amount < 0 ) {
                     r.cpu_amount = -cpu_balance;
                     cpu_balance.amount = 0;
                  } else {
                     r.cpu_amount = asset( 0, core_symbol() );
                  }
                  r.request_time = current_time_point();
               });
               need_deferred_trx = true;
            } // else stake increase requested with no existing row in refunds_tbl -> nothing to do with refunds_tbl
         } /// end if is_delegating_to_self || is_undelegating

         if ( need_deferred_trx ) {
            eosio::transaction out;
            out.actions.emplace_back( permission_level{from, active_permission},
                                      _self, "refund"_n,
                                      from
            );
            out.delay_sec = refund_delay_sec;
            cancel_deferred( from.value ); // TODO: Remove this line when replacing deferred trxs is fixed
            out.send( from.value, from, true );
         } else {
            cancel_deferred( from.value );
         }

         auto transfer_amount = net_balance + cpu_balance;
         if ( 0 < transfer_amount.amount ) {
            INLINE_ACTION_SENDER(eosio::token, transfer)(
               token_account, { {source_stake_from, active_permission} },
               { source_stake_from, stake_account, asset(transfer_amount), std::string("stake bandwidth") }
            );
         }
      }

      // update voting power
      {
         asset total_update = stake_net_delta + stake_cpu_delta;
         auto from_voter = _voters.find( from.value );
         if( from_voter == _voters.end() ) {
            from_voter = _voters.emplace( from, [&]( auto& v ) {
                  v.owner  = from;
                  v.staked = total_update.amount;
               });
         } else {
            _voters.modify( from_voter, same_payer, [&]( auto& v ) {
                  v.staked += total_update.amount;
               });
         }
         eosio_assert( 0 <= from_voter->staked, "stake for voting cannot be negative");
         if( from == "b1"_n ) {
            validate_b1_vesting( from_voter->staked );
         }

         if( from_voter->producers.size() || from_voter->proxy ) {
            update_votes( from, from_voter->proxy, from_voter->producers, false );
         }
      }
   }

   void system_contract::awardgenesis( name receiver, const asset tokens, uint64_t nonce )
   {
     require_auth(genesis_account);

     genesis_nonce_table genesis_nonce_tbl(_self, _self.value);
     auto it = genesis_nonce_tbl.find(nonce);
     eosio_assert(it == genesis_nonce_tbl.end(), "Duplicated call: nonce already exists.");
     genesis_nonce_tbl.emplace(genesis_account, [&]( auto& genesis_nonce ){
        genesis_nonce.nonce = nonce;
        genesis_nonce.awarded = tokens;
        genesis_nonce.receiver = receiver;
     });

     send_genesis_token( genesis_account, receiver, tokens, true);
   }

   void system_contract::delgenesis( uint64_t nonce )
   {
      require_auth(genesis_account);

      genesis_nonce_table genesis_nonce_tbl(_self, _self.value);
      auto it = genesis_nonce_tbl.find(nonce);
      eosio_assert(it != genesis_nonce_tbl.end(), "Nonce does not exists.");
      asset tokens = it->awarded;
      name receiver = it->receiver;
      genesis_nonce_tbl.erase(it);
     
      const asset zero_asset( 0, core_symbol() );

      del_bandwidth_table del_bw_tbl( _self, receiver.value );
      auto del_bw_itr = del_bw_tbl.find( receiver.value );
      
      if( del_bw_itr != del_bw_tbl.end() ) {
         auto from_net = std::min(del_bw_itr->net_weight, tokens);
         auto from_cpu = std::min(del_bw_itr->cpu_weight, tokens - from_net);
         
         if(from_net != zero_asset || from_cpu != zero_asset) {
            INLINE_ACTION_SENDER(system_contract, undelegatebw)(
            _self, { {receiver, active_permission} },
            { receiver, receiver, from_net, from_cpu });
         }
      }

      INLINE_ACTION_SENDER( system_contract, removerefund)(
            _self, { {_self, active_permission} },
            { receiver, tokens });
   }

   void system_contract::removerefund( const name account, const asset tokens )
   {
      require_auth(_self);

      const asset zero_asset( 0, core_symbol() );
      refunds_table refunds_tbl( _self, account.value );
      auto& req = refunds_tbl.get( account.value, "no refund found");
      eosio_assert(req.net_amount + req.cpu_amount >= tokens, "account does not have enough staked tokens");

      if(req.net_amount + req.cpu_amount == tokens){
         refunds_tbl.erase(req);
         return;
      }

      refunds_tbl.modify( req, same_payer, [&]( auto& r ) {
         if(req.net_amount >= tokens) {
            r.net_amount -= tokens;
         }else{
            r.cpu_amount -= tokens - req.net_amount;
            r.net_amount = zero_asset;
         }
      });
   }

   void system_contract::send_genesis_token( name from, name receiver, const asset tokens, bool add_backward_rewards ){
      const time_point ct = std::max(current_time_point(), gbm_initial_time);

      eosio_assert( is_account( receiver ), "receiver account does not exist");
      eosio_assert( tokens.is_valid(), "invalid tokens" );
      eosio_assert( tokens.amount > 0, "award quantity must be positive" );
      eosio_assert( tokens.symbol == core_symbol(), "only system tokens allowed" );

      asset backward_rewards = asset(0, core_symbol());
      if (add_backward_rewards && current_time_point() > gbm_initial_time) {
         const int64_t elapsed_useconds = (current_time_point() - gbm_initial_time).count();
         backward_rewards = asset(static_cast<int64_t>(tokens.amount * (elapsed_useconds / double(useconds_in_gbm_period))), core_symbol());
      }

      genesis_balance_table genesis_tbl( _self, receiver.value );
      auto itr = genesis_tbl.find( core_symbol().code().raw() );

      if( itr == genesis_tbl.end() ) {
         itr = genesis_tbl.emplace( genesis_account, [&]( auto& genesis_token ){
               genesis_token.last_updated      = ct;
               genesis_token.last_claim_time   = ct;
               genesis_token.balance           = tokens;
               genesis_token.unclaimed_balance = backward_rewards;
         });
      }
      else {
         const auto unclaimed_balance = get_unclaimed_gbm_balance(receiver);
         genesis_tbl.modify( itr, genesis_account, [&]( auto& genesis_token ){
               genesis_token.balance += tokens;
               genesis_token.unclaimed_balance = asset(unclaimed_balance, core_symbol()) + backward_rewards;
               genesis_token.last_updated = ct;
         });
      }

      auto net_amount = tokens.amount / 2;
      asset to_net(net_amount, core_symbol());
      asset to_cpu(tokens.amount - net_amount, core_symbol());

      INLINE_ACTION_SENDER(system_contract, delegatebw)(
            _self, { {from, active_permission}, {receiver, active_permission} },
            { from, receiver, to_net, to_cpu, true }
         );
   }

   int64_t system_contract::get_unclaimed_gbm_balance( name claimer )
   {
      if (current_time_point() <= gbm_initial_time) {
         return 0;
      }
      genesis_balance_table genesis_tbl( _self, claimer.value );
      const auto& genesis_tbl_row = genesis_tbl.get( core_symbol().code().raw(), "no genesis balance object found" );
      const auto claim_time = std::min(current_time_point(), gbm_final_time);

      if (claim_time <= genesis_tbl_row.last_updated) {
         return 0;
      }

      const int64_t elapsed_useconds = (claim_time - genesis_tbl_row.last_updated).count();
      const int64_t unclaimed_balance = static_cast<int64_t>(genesis_tbl_row.balance.amount * (elapsed_useconds / double(useconds_in_gbm_period)))  + genesis_tbl_row.unclaimed_balance.amount;
      return unclaimed_balance;
   }

   void system_contract::claimgenesis( name claimer )
   {
      require_auth(claimer);
      const auto ct = current_time_point();

      genesis_balance_table genesis_tbl( _self, claimer.value );

      const auto& claimer_balance = genesis_tbl.get( core_symbol().code().raw(), "no genesis balance object found" );
      eosio_assert( ct - claimer_balance.last_claim_time > microseconds(useconds_per_day) , "already claimed rewards within past day" );

      const auto unclaimed_balance = get_unclaimed_gbm_balance(claimer);
      eosio_assert( unclaimed_balance > 0, "nothing to claim" );

      const asset zero_asset( 0, core_symbol() );

      if( claimer_balance.balance == zero_asset){
         genesis_tbl.erase(claimer_balance);
      }else{
         genesis_tbl.modify( claimer_balance, claimer, [&]( auto& cb ) {
            // current time point truncated to days
            cb.last_claim_time   = ct;
            cb.last_updated      = ct;
            cb.unclaimed_balance = zero_asset;
         });
      }
 
      // Deal with paying
      const asset payable_rewards ( unclaimed_balance, core_symbol() );

      INLINE_ACTION_SENDER(eosio::token, transfer)(
         token_account, { {genesis_account, "active"_n} },
         { genesis_account, claimer, payable_rewards, std::string("claimgenesis") }
      );
   }

   bool system_contract::has_genesis_balance( name owner )
   {
       genesis_balance_table genesis_tbl( _self, owner.value );
       const auto & owner_genesis = genesis_tbl.find( core_symbol().code().raw() );
       return owner_genesis != genesis_tbl.end() && owner_genesis->balance.amount > 0;
   }

   void system_contract::change_genesis( name owner )
   {
     // Unstaked amount could be greater than TOKENS DELEGATED TO SELF
     // If this is the case, GENESIS BALANCE should be reduced by the DIFFERENCE:
     // DIFF = AMOUNT_BEING_UNSTAKED - TOKENS_DELEGATED_TO_SELF
     // NEW_GENESIS_BALANCE = PREVIOUS_GENESIS_BALANCE - DIFF
     // be aware that if AMOUNT_BEING_UNSTAKED > TOKENS_DELEGATED_TO_SELF,
     // the call to changebw() just above will fail due to unsufficient tokens

     // Since changebw succedded, receiver had enough delegated_to_self_tokens,
     // and now we should check if receiver also has a genesis balance which might
     // be decreased by DIFF (above defined)

     // Let's check receiver HAS a genesis balance
     if( has_genesis_balance(owner) ) {

       genesis_balance_table genesis_tbl( _self, owner.value );
       const auto & owner_genesis = genesis_tbl.get( core_symbol().code().raw(), "no balance object found");

       const auto unclaimed_balance = get_unclaimed_gbm_balance(owner);

       const asset zero_asset( 0, core_symbol() );

       del_bandwidth_table del_bw_tbl( _self, owner.value );
       auto del_bw_itr = del_bw_tbl.find( owner.value );
       genesis_tbl.modify( owner_genesis, owner, [&]( auto& genesis ){
         genesis.unclaimed_balance = asset(unclaimed_balance, core_symbol());
         genesis.last_updated    = current_time_point();
         if(del_bw_itr == del_bw_tbl.end()) {
            genesis.balance = zero_asset; // receiver consumed all her tokens an row will be erased
         } else {
            // receiver consumed shorter amount than available delegated_to_self_tokens
            // if remaining amount is greater or equal than genesis balance
            // -> genesis balance should stay unchanged
            // else (remaining amount is less than genesis balance )
            // -> genesis balance is now decreased to new_delegated_to_self_tokens amount
            genesis.balance = std::min<asset>(del_bw_itr->net_weight + del_bw_itr->cpu_weight, genesis.balance);
         }
       });

       if( owner_genesis.balance == zero_asset && owner_genesis.unclaimed_balance == zero_asset){
           genesis_tbl.erase(owner_genesis);
       }
     }
   }

   void system_contract::delegatebw( name from, name receiver,
                                     asset stake_net_quantity,
                                     asset stake_cpu_quantity, bool transfer )
   {
      asset zero_asset( 0, core_symbol() );
      eosio_assert( stake_cpu_quantity >= zero_asset, "must stake a positive amount" );
      eosio_assert( stake_net_quantity >= zero_asset, "must stake a positive amount" );
      eosio_assert( stake_net_quantity.amount + stake_cpu_quantity.amount > 0, "must stake a positive amount" );
      eosio_assert( !transfer || from != receiver, "cannot use transfer flag if delegating to self" );

      changebw( from, receiver, stake_net_quantity, stake_cpu_quantity, transfer);
   } // delegatebw

   void system_contract::undelegatebw( name from, name receiver,
                                       asset unstake_net_quantity, asset unstake_cpu_quantity )
   {
      asset zero_asset( 0, core_symbol() );
      eosio_assert( unstake_cpu_quantity >= zero_asset, "must unstake a positive amount" );
      eosio_assert( unstake_net_quantity >= zero_asset, "must unstake a positive amount" );
      eosio_assert( unstake_cpu_quantity.amount + unstake_net_quantity.amount > 0, "must unstake a positive amount" );
      eosio_assert( _gstate.total_activated_stake >= min_activated_stake,
                    "cannot undelegate bandwidth until the chain is activated (at least 15% of all tokens participate in voting)" );

      changebw( from, receiver, -unstake_net_quantity, -unstake_cpu_quantity, false);

      // deal with genesis balance
      change_genesis(receiver);
   } // undelegatebw

   void system_contract::refund( const name owner ) {
      require_auth( owner );

      refunds_table refunds_tbl( _self, owner.value );
      auto req = refunds_tbl.find( owner.value );
      eosio_assert( req != refunds_tbl.end(), "refund request not found" );
      eosio_assert( req->request_time + seconds(refund_delay_sec) <= current_time_point(),
                    "refund is not available yet" );

      INLINE_ACTION_SENDER(eosio::token, transfer)(
         token_account, { {stake_account, active_permission}, {req->owner, active_permission} },
         { stake_account, req->owner, req->net_amount + req->cpu_amount, std::string("unstake") }
      );

      refunds_tbl.erase( req );
   }


} //namespace eosiosystem
