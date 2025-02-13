#include <eosio/datastream.hpp>
#include <eosio/eosio.hpp>
#include <eosio/multi_index.hpp>
#include <eosio/privileged.hpp>
#include <eosio/serialize.hpp>
#include <eosio/transaction.hpp>

#include <eosio.system/eosio.system.hpp>
#include <eosio.token/eosio.token.hpp>

namespace eosiosystem {

   using eosio::asset;
   using eosio::const_mem_fun;
   using eosio::current_time_point;
   using eosio::indexed_by;
   using eosio::permission_level;
   using eosio::seconds;
   using eosio::time_point_sec;
   using eosio::token;

   /**
    *  This action will buy an exact amount of ram and bill the payer the current market price.
    */
   action_return_buyram system_contract::buyrambytes( const name& payer, const name& receiver, uint32_t bytes ) {
      auto itr = _rammarket.find(ramcore_symbol.raw());
      const int64_t ram_reserve   = itr->base.balance.amount;
      const int64_t eos_reserve   = itr->quote.balance.amount;
      const int64_t cost          = exchange_state::get_bancor_input( ram_reserve, eos_reserve, bytes );
      const int64_t cost_plus_fee = cost / double(0.995);
      return buyram( payer, receiver, asset{ cost_plus_fee, core_symbol() } );
   }

   /**
    * Buy self ram action, ram can only be purchased to itself.
    */
   action_return_buyram system_contract::buyramself( const name& account, const asset& quant ) {
      return buyram( account, account, quant );
   }

   /**
    *  When buying ram the payer irreversibly transfers quant to system contract and only
    *  the receiver may reclaim the tokens via the sellram action. The receiver pays for the
    *  storage of all database records associated with this action.
    *
    *  RAM is a scarce resource whose supply is defined by global properties max_ram_size. RAM is
    *  priced using the bancor algorithm such that price-per-byte with a constant reserve ratio of 100:1.
    */
   action_return_buyram system_contract::buyram( const name& payer, const name& receiver, const asset& quant )
   {
      require_auth( payer );
      update_ram_supply();
      require_recipient(payer);
      require_recipient(receiver);

      check( quant.symbol == core_symbol(), "must buy ram with core token" );
      check( quant.amount > 0, "must purchase a positive amount" );

      auto fee = quant;
      fee.amount = ( fee.amount + 199 ) / 200; /// .5% fee (round up)
      // fee.amount cannot be 0 since that is only possible if quant.amount is 0 which is not allowed by the assert above.
      // If quant.amount == 1, then fee.amount == 1,
      // otherwise if quant.amount > 1, then 0 < fee.amount < quant.amount.
      auto quant_after_fee = quant;
      quant_after_fee.amount -= fee.amount;
      // quant_after_fee.amount should be > 0 if quant.amount > 1.
      // If quant.amount == 1, then quant_after_fee.amount == 0 and the next inline transfer will fail causing the buyram action to fail.
      {
         token::transfer_action transfer_act{ token_account, { {payer, active_permission}, {ram_account, active_permission} } };
         transfer_act.send( payer, ram_account, quant_after_fee, "buy ram" );
      }
      if ( fee.amount > 0 ) {
         token::transfer_action transfer_act{ token_account, { {payer, active_permission} } };
         transfer_act.send( payer, ramfee_account, fee, "ram fee" );
      }

      int64_t bytes_out;

      const auto& market = _rammarket.get(ramcore_symbol.raw(), "ram market does not exist");
      _rammarket.modify( market, same_payer, [&]( auto& es ) {
         bytes_out = es.direct_convert( quant_after_fee,  ram_symbol ).amount;
      });

      check( bytes_out > 0, "must reserve a positive amount" );

      _gstate.total_ram_bytes_reserved += uint64_t(bytes_out);
      _gstate.total_ram_stake          += quant_after_fee.amount;

      const int64_t ram_bytes = add_ram( receiver, bytes_out );

      // // logging
      system_contract::logbuyram_action logbuyram_act{ get_self(), { {get_self(), active_permission} } };
      system_contract::logsystemfee_action logsystemfee_act{ get_self(), { {get_self(), active_permission} } };

      logbuyram_act.send( payer, receiver, quant, bytes_out, ram_bytes, fee );
      logsystemfee_act.send( ram_account, fee, "buy ram" );

      // action return value
      return action_return_buyram{ payer, receiver, quant, bytes_out, ram_bytes, fee };
   }

   void system_contract::logbuyram( const name& payer, const name& receiver, const asset& quantity, int64_t bytes, int64_t ram_bytes, const asset& fee ) {
      require_auth( get_self() );
      require_recipient(payer);
      require_recipient(receiver);
   }

  /**
    *  The system contract now buys and sells RAM allocations at prevailing market prices.
    *  This may result in traders buying RAM today in anticipation of potential shortages
    *  tomorrow. Overall this will result in the market balancing the supply and demand
    *  for RAM over time.
    */
   action_return_sellram system_contract::sellram( const name& account, int64_t bytes ) {
      require_auth( account );
      update_ram_supply();
      require_recipient(account);
      const int64_t ram_bytes = reduce_ram(account, bytes);

      asset tokens_out;
      auto itr = _rammarket.find(ramcore_symbol.raw());
      _rammarket.modify( itr, same_payer, [&]( auto& es ) {
         /// the cast to int64_t of bytes is safe because we certify bytes is <= quota which is limited by prior purchases
         tokens_out = es.direct_convert( asset(bytes, ram_symbol), core_symbol());
      });

      check( tokens_out.amount > 1, "token amount received from selling ram is too low" );

      _gstate.total_ram_bytes_reserved -= static_cast<decltype(_gstate.total_ram_bytes_reserved)>(bytes); // bytes > 0 is asserted above
      _gstate.total_ram_stake          -= tokens_out.amount;

      //// this shouldn't happen, but just in case it does we should prevent it
      check( _gstate.total_ram_stake >= 0, "error, attempt to unstake more tokens than previously staked" );

      {
         token::transfer_action transfer_act{ token_account, { {ram_account, active_permission}, {account, active_permission} } };
         transfer_act.send( ram_account, account, asset(tokens_out), "sell ram" );
      }
      auto fee = ( tokens_out.amount + 199 ) / 200; /// .5% fee (round up)
      // since tokens_out.amount was asserted to be at least 2 earlier, fee.amount < tokens_out.amount
      if ( fee > 0 ) {
         token::transfer_action transfer_act{ token_account, { {account, active_permission} } };
         transfer_act.send( account, ramfee_account, asset(fee, core_symbol()), "sell ram fee" );
      }

      // logging
      system_contract::logsellram_action logsellram_act{ get_self(), { {get_self(), active_permission} } };
      system_contract::logsystemfee_action logsystemfee_act{ get_self(), { {get_self(), active_permission} } };

      logsellram_act.send( account, tokens_out, bytes, ram_bytes, asset(fee, core_symbol() ) );
      logsystemfee_act.send( ram_account, asset(fee, core_symbol() ), "sell ram" );

      // action return value
      return action_return_sellram{ account, tokens_out, bytes, ram_bytes, asset(fee, core_symbol() ) };
   }

   void system_contract::logsellram( const name& account, const asset& quantity, int64_t bytes, int64_t ram_bytes, const asset& fee ) {
      require_auth( get_self() );
      require_recipient(account);
   }

    /**
    * This action will transfer RAM bytes from one account to another.
    */
   action_return_ramtransfer system_contract::ramtransfer( const name& from, const name& to, int64_t bytes, const std::string& memo ) {
      require_auth( from );
      update_ram_supply();
      check( memo.size() <= 256, "memo has more than 256 bytes" );
      const int64_t from_ram_bytes = reduce_ram( from, bytes );
      const int64_t to_ram_bytes = add_ram( to, bytes );
      require_recipient( from );
      require_recipient( to );

      // action return value
      return action_return_ramtransfer{ from, to, bytes, from_ram_bytes, to_ram_bytes };
   }

   /**
    * This action will burn RAM bytes from owner account.
    */
   action_return_ramtransfer system_contract::ramburn( const name& owner, int64_t bytes, const std::string& memo ) {
      require_auth( owner );
      return ramtransfer( owner, null_account, bytes, memo );
   }

   /**
    * This action will buy and then burn the purchased RAM bytes.
    */
   action_return_buyram system_contract::buyramburn( const name& payer, const asset& quantity, const std::string& memo ) {
      require_auth( payer );
      check( quantity.symbol == core_symbol(), "quantity must be core token" );
      check( quantity.amount > 0, "quantity must be positive" );

      const auto return_buyram = buyram( payer, payer, quantity );
      ramburn( payer, return_buyram.bytes_purchased, memo );

      return return_buyram;
   }

   [[eosio::action]]
   void system_contract::logramchange( const name& owner, int64_t bytes, int64_t ram_bytes )
   {
      require_auth( get_self() );
      require_recipient( owner );
   }

   int64_t system_contract::reduce_ram( const name& owner, int64_t bytes ) {
      check( bytes > 0, "cannot reduce negative byte" );
      user_resources_table userres( get_self(), owner.value );
      auto res_itr = userres.find( owner.value );
      check( res_itr != userres.end(), "no resource row" );
      check( res_itr->ram_bytes >= bytes, "insufficient quota" );

      userres.modify( res_itr, same_payer, [&]( auto& res ) {
          res.ram_bytes -= bytes;
      });
      set_resource_ram_bytes_limits( owner );

      // logging
      system_contract::logramchange_action logramchange_act{ get_self(), { {get_self(), active_permission} }};
      logramchange_act.send( owner, -bytes, res_itr->ram_bytes );
      return res_itr->ram_bytes;
   }

   int64_t system_contract::add_ram( const name& owner, int64_t bytes ) {
      check( bytes > 0, "cannot add negative byte" );
      check( is_account(owner), "owner=" + owner.to_string() + " account does not exist");
      user_resources_table userres( get_self(), owner.value );
      auto res_itr = userres.find( owner.value );
      if ( res_itr == userres.end() ) {
         userres.emplace( owner, [&]( auto& res ) {
            res.owner = owner;
            res.net_weight = asset( 0, core_symbol() );
            res.cpu_weight = asset( 0, core_symbol() );
            res.ram_bytes = bytes;
         });
      } else {
         userres.modify( res_itr, same_payer, [&]( auto& res ) {
            res.ram_bytes += bytes;
         });
      }
      set_resource_ram_bytes_limits( owner );

      // logging
      system_contract::logramchange_action logramchange_act{ get_self(), { {get_self(), active_permission} } };
      logramchange_act.send( owner, bytes, res_itr->ram_bytes );
      return res_itr->ram_bytes;
   }

   void system_contract::set_resource_ram_bytes_limits( const name& owner ) {
      user_resources_table userres( get_self(), owner.value );
      auto res_itr = userres.find( owner.value );

      auto voter_itr = _voters.find( owner.value );
      if ( voter_itr == _voters.end() || !has_field( voter_itr->flags1, voter_info::flags1_fields::ram_managed ) ) {
         int64_t ram_bytes, net, cpu;
         get_resource_limits( owner, ram_bytes, net, cpu );
         set_resource_limits( owner, res_itr->ram_bytes + ram_gift_bytes, net, cpu );
      }
   }

   void validate_b1_vesting( int64_t stake ) {
      const int64_t base_time = 1527811200; /// Friday, June 1, 2018 12:00:00 AM UTC
      const int64_t max_claimable = 100'000'000'0000ll;
      const int64_t claimable = int64_t(max_claimable * double(current_time_point().sec_since_epoch() - base_time) / (10*seconds_per_year) );

      check( max_claimable - claimable <= stake, "b1 can only claim their tokens over 10 years" );
   }

   void system_contract::changebw( name from, const name& receiver,
                                   const asset& stake_net_delta, const asset& stake_cpu_delta, bool transfer )
   {
      require_auth( from );
      check( stake_net_delta.amount != 0 || stake_cpu_delta.amount != 0, "should stake non-zero amount" );
      check( std::abs( (stake_net_delta + stake_cpu_delta).amount )
             >= std::max( std::abs( stake_net_delta.amount ), std::abs( stake_cpu_delta.amount ) ),
             "net and cpu deltas cannot be opposite signs" );

      name source_stake_from = from;
      if ( transfer ) {
         from = receiver;
      }

      // update stake delegated from "from" to "receiver"
      {
         del_bandwidth_table     del_tbl( get_self(), from.value );
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
         check( 0 <= itr->net_weight.amount, "insufficient staked net bandwidth" );
         check( 0 <= itr->cpu_weight.amount, "insufficient staked cpu bandwidth" );
         if ( itr->is_empty() ) {
            del_tbl.erase( itr );
         }
      } // itr can be invalid, should go out of scope

      // update totals of "receiver"
      {
         user_resources_table   totals_tbl( get_self(), receiver.value );
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
         check( 0 <= tot_itr->net_weight.amount, "insufficient staked total net bandwidth" );
         check( 0 <= tot_itr->cpu_weight.amount, "insufficient staked total cpu bandwidth" );

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
               get_resource_limits( receiver, ram_bytes, net, cpu );

               set_resource_limits( receiver,
                                    ram_managed ? ram_bytes : std::max( tot_itr->ram_bytes + ram_gift_bytes, ram_bytes ),
                                    net_managed ? net : tot_itr->net_weight.amount,
                                    cpu_managed ? cpu : tot_itr->cpu_weight.amount );
            }
         }

         if ( tot_itr->is_empty() ) {
            totals_tbl.erase( tot_itr );
         }
      } // tot_itr can be invalid, should go out of scope

      // create refund or update from existing refund
      if ( stake_account != source_stake_from ) { //for eosio both transfer and refund make no sense
         refunds_table refunds_tbl( get_self(), from.value );
         auto req = refunds_tbl.find( from.value );

         //create/update/delete refund
         auto net_balance = stake_net_delta;
         auto cpu_balance = stake_cpu_delta;


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

               check( 0 <= req->net_amount.amount, "negative net refund amount" ); //should never happen
               check( 0 <= req->cpu_amount.amount, "negative cpu refund amount" ); //should never happen

               if ( req->is_empty() ) {
                  refunds_tbl.erase( req );
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
            } // else stake increase requested with no existing row in refunds_tbl -> nothing to do with refunds_tbl
         } /// end if is_delegating_to_self || is_undelegating

         auto transfer_amount = net_balance + cpu_balance;
         if ( 0 < transfer_amount.amount ) {
            token::transfer_action transfer_act{ token_account, { {source_stake_from, active_permission} } };
            transfer_act.send( source_stake_from, stake_account, asset(transfer_amount), "stake bandwidth" );
         }
      }

      _wps_state.total_stake += (stake_net_delta.amount + stake_cpu_delta.amount);

      update_voting_power( from, stake_net_delta + stake_cpu_delta );
   }

   void system_contract::removerefund( const name account, const asset tokens )
   {
      require_auth(_self);

      const asset zero_asset( 0, core_symbol() );
      refunds_table refunds_tbl( _self, account.value );
      auto& req = refunds_tbl.get( account.value, "no refund found");
      check(req.net_amount + req.cpu_amount >= tokens, "account does not have enough staked tokens");

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

   void system_contract::update_voting_power( const name& voter, const asset& total_update )
   {
      auto voter_itr = _voters.find( voter.value );
      if( voter_itr == _voters.end() ) {
         voter_itr = _voters.emplace( voter, [&]( auto& v ) {
            v.owner  = voter;
            v.staked = total_update.amount;
         });
      } else {
         _voters.modify( voter_itr, same_payer, [&]( auto& v ) {
            v.staked += total_update.amount;
         });
      }

      check( 0 <= voter_itr->staked, "stake for voting cannot be negative" );

      if( voter == "b1"_n ) {
         validate_b1_vesting( voter_itr->staked );
      }

      if( voter_itr->producers.size() || voter_itr->proxy ) {
         update_votes( voter, voter_itr->proxy, voter_itr->producers, false );
      }

      auto wps_voter_itr = _wpsvoters.find( voter.value );
      if(wps_voter_itr != _wpsvoters.end()){
         update_wps_votes( voter, wps_voter_itr->proposals);
      }
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
         return genesis_tbl_row.unclaimed_balance.amount;
      }

      const int64_t elapsed_useconds = (claim_time - genesis_tbl_row.last_updated).count();
      const int64_t unclaimed_balance = static_cast<int64_t>(genesis_tbl_row.balance.amount * (elapsed_useconds / double(useconds_in_gbm_period))) + genesis_tbl_row.unclaimed_balance.amount;
      return unclaimed_balance;
   }

   void system_contract::claimgenesis( name claimer )
   {
      require_auth(claimer);
      const auto ct = current_time_point();

      genesis_balance_table genesis_tbl( _self, claimer.value );

      const auto& claimer_balance = genesis_tbl.get( core_symbol().code().raw(), "no genesis balance object found" );
      check( ct - claimer_balance.last_claim_time > eosio::microseconds(useconds_per_day) , "already claimed rewards within past day" );

      const auto unclaimed_balance = get_unclaimed_gbm_balance(claimer);
      check( unclaimed_balance > 0, "nothing to claim" );

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

      token::transfer_action transfer_act{ token_account, { {genesis_account, "active"_n} } };
      transfer_act.send(genesis_account, claimer, payable_rewards, std::string("claimgenesis"));
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
       // withdrawn_genesis represents the amount of genesis affected by unstaking.
       asset withdrawn_genesis;

       del_bandwidth_table del_bw_tbl( _self, owner.value );
       auto del_bw_itr = del_bw_tbl.find( owner.value );
       genesis_tbl.modify( owner_genesis, owner, [&]( auto& genesis ){
         genesis.unclaimed_balance = asset(unclaimed_balance, core_symbol());
         genesis.last_updated    = current_time_point();
         if(del_bw_itr == del_bw_tbl.end()) {
            withdrawn_genesis = genesis.balance;
            genesis.balance = zero_asset; // receiver consumed all her tokens an row will be erased
         } else {
            // receiver consumed shorter amount than available delegated_to_self_tokens
            // if remaining amount is greater or equal than genesis balance
            // -> genesis balance should stay unchanged
            // else (remaining amount is less than genesis balance )
            // -> genesis balance is now decreased to new_delegated_to_self_tokens amount
            const auto prev_genesis = genesis.balance;
            genesis.balance = std::min<asset>(del_bw_itr->net_weight + del_bw_itr->cpu_weight, genesis.balance);
            withdrawn_genesis = prev_genesis - genesis.balance;
         }
       });

       if( owner_genesis.balance == zero_asset && owner_genesis.unclaimed_balance == zero_asset){
           genesis_tbl.erase(owner_genesis);
       }

       const auto unstake_time = std::min(current_time_point(), gbm_final_time);
       const int64_t delta_time_usec = (gbm_final_time - unstake_time).count();
       int64_t to_burn_amount = static_cast<int64_t>(withdrawn_genesis.amount * (delta_time_usec / double(useconds_in_gbm_period)));

       if (to_burn_amount > 0) {
         const asset to_burn(to_burn_amount, core_symbol());
         token::transfer_action transfer_act{ token_account, { {genesis_account, active_permission} } };
         transfer_act.send(genesis_account, get_self(), to_burn, "transfering back to eosio to burn pre-minted tokens from unstaking.");
         token::retire_action retire_act{ token_account, { {get_self(), active_permission} } };
         retire_act.send(to_burn, "to burn pre-minted tokens from unstaking.");
       }
     }
   }

   void system_contract::delegatebw( const name& from, const name& receiver,
                                     const asset& stake_net_quantity,
                                     const asset& stake_cpu_quantity, bool transfer )
   {
      asset zero_asset( 0, core_symbol() );
      check( stake_cpu_quantity >= zero_asset, "must stake a positive amount" );
      check( stake_net_quantity >= zero_asset, "must stake a positive amount" );
      check( stake_net_quantity.amount + stake_cpu_quantity.amount > 0, "must stake a positive amount" );
      check( !transfer || from != receiver, "cannot use transfer flag if delegating to self" );

      changebw( from, receiver, stake_net_quantity, stake_cpu_quantity, transfer);
   } // delegatebw

   void system_contract::undelegatebw( const name& from, const name& receiver,
                                       const asset& unstake_net_quantity, const asset& unstake_cpu_quantity )
   {
      asset zero_asset( 0, core_symbol() );
      check( unstake_cpu_quantity >= zero_asset, "must unstake a positive amount" );
      check( unstake_net_quantity >= zero_asset, "must unstake a positive amount" );
      check( unstake_cpu_quantity.amount + unstake_net_quantity.amount > 0, "must unstake a positive amount" );
      check( _gstate.thresh_activated_stake_time != time_point(),
             "cannot undelegate bandwidth until the chain is activated (at least 15% of all tokens participate in voting)" );

      changebw( from, receiver, -unstake_net_quantity, -unstake_cpu_quantity, false);

      // deal with genesis balance
      change_genesis(receiver);
   } // undelegatebw


   void system_contract::refund( const name& owner ) {
      require_auth( owner );

      refunds_table refunds_tbl( get_self(), owner.value );
      auto req = refunds_tbl.find( owner.value );
      check( req != refunds_tbl.end(), "refund request not found" );
      check( req->request_time + seconds(refund_delay_sec) <= current_time_point(),
             "refund is not available yet" );
      token::transfer_action transfer_act{ token_account, { {stake_account, active_permission}, {req->owner, active_permission} } };
      transfer_act.send( stake_account, req->owner, req->net_amount + req->cpu_amount, "unstake" );
      refunds_tbl.erase( req );
   }


} //namespace eosiosystem
