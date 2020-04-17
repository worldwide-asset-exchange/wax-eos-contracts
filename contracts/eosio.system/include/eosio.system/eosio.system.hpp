#pragma once

#include <eosio/asset.hpp>
#include <eosio/privileged.hpp>
#include <eosio/singleton.hpp>
#include <eosio/system.hpp>
#include <eosio/time.hpp>

#include <eosio.system/exchange_state.hpp>
#include <eosio.system/native.hpp>

#include <deque>
#include <limits>
#include <optional>
#include <string>
#include <tuple>
#include <type_traits>
#include <utility>
#include <vector>
#include <cmath>


namespace eosiosystem {

   using eosio::asset;
   using eosio::block_timestamp;
   using eosio::check;
   using eosio::const_mem_fun;
   using eosio::datastream;
   using eosio::indexed_by;
   using eosio::name;
   using eosio::same_payer;
   using eosio::symbol;
   using eosio::symbol_code;
   using eosio::time_point;
   using eosio::time_point_sec;
   using eosio::unsigned_int;
   using std::string;
   using std::vector;
   using std::set;
   using std::optional;

   template<typename E, typename F>
   static inline auto has_field( F flags, E field )
   -> std::enable_if_t< std::is_integral_v<F> && std::is_unsigned_v<F> &&
                        std::is_enum_v<E> && std::is_same_v< F, std::underlying_type_t<E> >, bool>
   {
      return ( (flags & static_cast<F>(field)) != 0 );
   }

   template<typename E, typename F>
   static inline auto set_field( F flags, E field, bool value = true )
   -> std::enable_if_t< std::is_integral_v<F> && std::is_unsigned_v<F> &&
                        std::is_enum_v<E> && std::is_same_v< F, std::underlying_type_t<E> >, F >
   {
      if( value )
         return ( flags | static_cast<F>(field) );
      else
         return ( flags & ~static_cast<F>(field) );
   }

   template<typename EnumType, typename IntType = std::underlying_type_t<EnumType>>
   IntType enum_cast(EnumType value) {
      return static_cast<IntType>(value);
   }

   static constexpr uint32_t seconds_per_year      = 52 * 7 * 24 * 3600;
   static constexpr uint32_t seconds_per_day       = 24 * 3600;
   static constexpr int64_t  useconds_per_year     = int64_t(seconds_per_year) * 1000'000ll;
   static constexpr int64_t  useconds_per_day      = int64_t(seconds_per_day) * 1000'000ll;
   static constexpr uint32_t blocks_per_day        = 2 * seconds_per_day; // half seconds per day

   static constexpr int64_t  min_activated_stake   = 150'000'000'0000;
   static constexpr int64_t  ram_gift_bytes        = 1400;
   static constexpr int64_t  min_pervote_daily_pay = 100'0000;
   static constexpr double   continuous_rate       = 0.04879;          // 5% annual rate
   static constexpr int64_t  inflation_pay_factor  = 5;                // 20% of the inflation
   static constexpr int64_t  votepay_factor        = 4;                // 25% of the producer pay
   static constexpr uint32_t refund_delay_sec      = 3 * seconds_per_day;
   static constexpr uint32_t max_standbys          = 36;
   static constexpr uint32_t max_producers         = 21;
   static constexpr uint32_t blocks_per_round      = 12;
   static constexpr double   producer_perc_reward  = 0.60;
   static constexpr double   standby_perc_reward   = 1 - producer_perc_reward;
   static constexpr double   standby_perc_blocks   = 1.0;              // Standby's will be selected for 1% of block production
   static constexpr uint32_t num_performance_producers = 16;
   static constexpr uint32_t producer_performances_window = 1000;

   static constexpr uint32_t default_producer_blocks_performance_window = 56 * blocks_per_round; // default approx 2 hours, since it will typically take a producer 1 minute to be called into production
   static constexpr uint32_t default_standby_blocks_performance_window = 3 * blocks_per_round;  // default approx 18 hours, since it will typically take each standby 6 hours to be randomly called into production


   static constexpr uint64_t useconds_in_gbm_period = 1096 * useconds_per_day;   // from July 1st 2019 to July 1st 2022
   static const time_point gbm_initial_time(eosio::seconds(1561939200));     // July 1st 2019 00:00:00
   static const time_point gbm_final_time = gbm_initial_time + eosio::microseconds(useconds_in_gbm_period);   // July 1st 2022 00:00:00

   /**
    *
    * @defgroup eosiosystem eosio.system
    * @ingroup eosiocontracts
    * eosio.system contract defines the structures and actions needed for blockchain's core functionality.
    * - Users can stake tokens for CPU and Network bandwidth, and then vote for producers or
    *    delegate their vote to a proxy.
    * - Producers register in order to be voted for, and can claim per-block and per-vote rewards.
    * - Users can buy and sell RAM at a market-determined price.
    * - Users can bid on premium names.
    * - A resource exchange system (REX) allows token holders to lend their tokens,
    *    and users to rent CPU and Network resources in return for a market-determined fee.
    * @{
    */

   /**
    * Type of rewards
    * 
    * @details Defines types of rewards for all producers and also the current 
    *          reward status. 
    */
   enum class reward_type: uint32_t {
      none = 0,
      producer = 1,
      standby = 2
   };

   using prod_vec_t = std::vector<std::tuple<eosio::producer_key, uint16_t /* location */, reward_type>>;
   // Note: we use uint32_t rather than reward_type because enum's cannot be serialized
   using top_prod_vec_t = std::vector<std::pair<eosio::name /* owner */, uint32_t /* reward_type */ >>;

   /**
    * A name bid.
    *
    * @details A name bid consists of:
    * - a `newname` name that the bid is for
    * - a `high_bidder` account name that is the one with the highest bid so far
    * - the `high_bid` which is amount of highest bid
    * - and `last_bid_time` which is the time of the highest bid
    */
   struct [[eosio::table, eosio::contract("eosio.system")]] name_bid {
     name            newname;
     name            high_bidder;
     int64_t         high_bid = 0; ///< negative high_bid == closed auction waiting to be claimed
     time_point      last_bid_time;

     uint64_t primary_key()const { return newname.value;                    }
     uint64_t by_high_bid()const { return static_cast<uint64_t>(-high_bid); }
   };

   /**
    * A bid refund.
    *
    * @details A bid refund is defined by:
    * - the `bidder` account name owning the refund
    * - the `amount` to be refunded
    */
   struct [[eosio::table, eosio::contract("eosio.system")]] bid_refund {
      name         bidder;
      asset        amount;

      uint64_t primary_key()const { return bidder.value; }
   };

   /**
    * Name bid table
    *
    * @details The name bid table is storing all the `name_bid`s instances.
    */
   typedef eosio::multi_index< "namebids"_n, name_bid,
                               indexed_by<"highbid"_n, const_mem_fun<name_bid, uint64_t, &name_bid::by_high_bid>  >
                             > name_bid_table;

   /**
    * Bid refund table.
    *
    * @details The bid refund table is storing all the `bid_refund`s instances.
    */
   typedef eosio::multi_index< "bidrefunds"_n, bid_refund > bid_refund_table;

   /**
    * Defines new global state parameters.
    */
   struct [[eosio::table("global"), eosio::contract("eosio.system")]] eosio_global_state : eosio::blockchain_parameters {
      uint64_t free_ram()const { return max_ram_size - total_ram_bytes_reserved; }

      uint64_t             max_ram_size = 64ll*1024 * 1024 * 1024;
      uint64_t             total_ram_bytes_reserved = 0;
      int64_t              total_ram_stake = 0;

      block_timestamp      last_producer_schedule_update;
      time_point           last_pervote_bucket_fill;
      int64_t              pervote_bucket = 0;
      int64_t              perblock_bucket = 0; /// @deprecated Deprecated once standby reward will be activated. See eosio_global_reward
      int64_t              voters_bucket = 0;
      double               total_voteshare_change_rate = 0;
      double               total_unpaid_voteshare = 0;   // Common fund to pay voters.
      time_point           total_unpaid_voteshare_last_updated;
      uint32_t             total_unpaid_blocks = 0; /// all blocks which have been produced but not paid
      int64_t              total_activated_stake = 0;
      time_point           thresh_activated_stake_time;
      uint16_t             last_producer_schedule_size = 0;
      double               total_producer_vote_weight = 0; /// the sum of all producer votes
      block_timestamp      last_name_close;

      // explicit serialization macro is not necessary, used here only to improve compilation time
      EOSLIB_SERIALIZE_DERIVED( eosio_global_state, eosio::blockchain_parameters,
                                (max_ram_size)(total_ram_bytes_reserved)(total_ram_stake)
                                (last_producer_schedule_update)(last_pervote_bucket_fill)
                                (pervote_bucket)(perblock_bucket)(voters_bucket)(total_voteshare_change_rate)
                                (total_unpaid_voteshare)(total_unpaid_voteshare_last_updated)(total_unpaid_blocks)
                                (total_activated_stake)(thresh_activated_stake_time)
                                (last_producer_schedule_size)(total_producer_vote_weight)(last_name_close) )
   };

   /**
    * Defines new global state parameters added after version 1.0
    */
   struct [[eosio::table("global2"), eosio::contract("eosio.system")]] eosio_global_state2 {
      eosio_global_state2(){}

      uint16_t          new_ram_per_block = 0;
      block_timestamp   last_ram_increase;
      block_timestamp   last_block_num;
      double            total_producer_votepay_share = 0;
      uint8_t           revision = 0; ///< used to track version updates in the future.

      EOSLIB_SERIALIZE( eosio_global_state2, (new_ram_per_block)(last_ram_increase)(last_block_num)
                        (total_producer_votepay_share)(revision) )
   };

   /**
    * Defines new global state parameters added after version 1.3.0
    */
   struct [[eosio::table("global3"), eosio::contract("eosio.system")]] eosio_global_state3 {
      eosio_global_state3() { }
      time_point        last_vpay_state_update;
      double            total_vpay_share_change_rate = 0;

      EOSLIB_SERIALIZE( eosio_global_state3, (last_vpay_state_update)(total_vpay_share_change_rate) )
   };

   /**
    * Global counters for producer/standby rewards
    */
   struct [[eosio::table("glbreward"), eosio::contract("eosio.system")]] eosio_global_reward {
      // A unique name is needed in order to avoid problems with ABI generator
      // which doesn't understand scopes (see rewards_info table)
      struct global_rewards_counter_type {
         uint64_t              total_unpaid_blocks = 0;
         int64_t               perblock_bucket = 0;
         uint64_t              block_count = 0;
      };

      bool activated = false;  // Producer/standby rewards activated 
      std::map<uint32_t /*reward_type*/, global_rewards_counter_type> counters;
      std::map<uint64_t /*version*/,     top_prod_vec_t> proposed_top_producers;
      top_prod_vec_t current_producers;

      // The number of blocks that will be used to sample each producer's performance making blocks
      uint32_t producer_blocks_performance_window = default_producer_blocks_performance_window;
      // Likewise for standbys
      uint32_t standby_blocks_performance_window = default_standby_blocks_performance_window;
      bool random_standby_selection = true; // turn randomized standby selection on/off
      uint64_t last_standby_index = 0;

      double avg_producer_performances = 0.5;

      void update_producer_performances(double new_performance) {
        avg_producer_performances = (new_performance + avg_producer_performances * (producer_performances_window - 1)) / producer_performances_window;
      }

      const double average_producer_performances() const {
        return avg_producer_performances;
      }

      eosio_global_reward() {
         for (auto type: { reward_type::none, reward_type::producer, reward_type::standby }) {
            counters.emplace(enum_cast(type), global_rewards_counter_type());
         }
      }

      const auto& get_counters(reward_type type) const {
         auto it = counters.find(enum_cast(type));
         check(it != counters.end(), "Cannot find counter data");
         return it->second;
      }

      auto& get_counters(reward_type type) {
         auto it = counters.find(enum_cast(type));
         check(it != counters.end(), "Cannot find counter data");
         return it->second;
      }

      void new_unpaid_block(reward_type type, const eosio::block_timestamp& tm) {
         auto& counters = get_counters(type);

         counters.total_unpaid_blocks++;
         counters.block_count++;
      }

      uint32_t get_performance_window(reward_type producer_type) {
        return producer_type == reward_type::producer
            ? producer_blocks_performance_window
            : standby_blocks_performance_window;
      }

      // explicit serialization macro is not necessary, used here only to improve compilation time
      EOSLIB_SERIALIZE( eosio_global_reward, (activated)(counters)(proposed_top_producers)(current_producers)(producer_blocks_performance_window)(standby_blocks_performance_window)(random_standby_selection)(last_standby_index)(avg_producer_performances))
   };

   /**
    * Defines `producer_info` structure to be stored in `producer_info` table, added after version 1.0
    */
   struct [[eosio::table, eosio::contract("eosio.system")]] producer_info {
      name                  owner;
      double                total_votes = 0;
      eosio::public_key     producer_key; /// a packed public key object
      bool                  is_active = true;
      std::string           url;
      uint32_t              unpaid_blocks = 0;  /// @deprecated Deprecated once standby reward will be activated. See reward_info table
      time_point            last_claim_time;
      uint16_t              location = 0;

      uint64_t primary_key()const { return owner.value;                             }
      double   by_votes()const    { return is_active ? -total_votes : total_votes;  }
      bool     active()const      { return is_active;                               }
      void     deactivate()       { producer_key = public_key(); is_active = false; }

      // explicit serialization macro is not necessary, used here only to improve compilation time
      EOSLIB_SERIALIZE( producer_info, (owner)(total_votes)(producer_key)(is_active)(url)
                        (unpaid_blocks)(last_claim_time)(location) )
   };

   /**
    * Defines new producer info structure to be stored in new producer info table, added after version 1.3.0
    */
   struct [[eosio::table, eosio::contract("eosio.system")]] producer_info2 {
      name            owner;
      double          votepay_share = 0;
      time_point      last_votepay_share_update;

      uint64_t primary_key()const { return owner.value; }

      // explicit serialization macro is not necessary, used here only to improve compilation time
      EOSLIB_SERIALIZE( producer_info2, (owner)(votepay_share)(last_votepay_share_update) )
   };

   /**
    * Voter info.
    *
    * @details Voter info stores information about the voter:
    * - `owner` the voter
    * - `proxy` the proxy set by the voter, if any
    * - `producers` the producers approved by this voter if no proxy set
    * - `staked` the amount staked
    */
   struct [[eosio::table, eosio::contract("eosio.system")]] voter_info {
      name                owner;     /// the voter
      name                proxy;     /// the proxy set by the voter, if any
      std::vector<name>   producers; /// the producers approved by this voter if no proxy set
      int64_t             staked = 0;

      double              unpaid_voteshare = 0;
      time_point          unpaid_voteshare_last_updated;
      double              unpaid_voteshare_change_rate;
      time_point          last_claim_time;

      /**
       *  Every time a vote is cast we must first "undo" the last vote weight, before casting the
       *  new vote weight.  Vote weight is calculated as:
       *
       *  stated.amount * 2 ^ ( weeks_since_launch/weeks_per_year)
       */
      double              last_vote_weight = 0; /// the vote weight cast the last time the vote was updated

      /**
       * Total vote weight delegated to this voter.
       */
      double              proxied_vote_weight= 0; /// the total vote weight delegated to this voter as a proxy
      bool                is_proxy = 0; /// whether the voter is a proxy for others


      uint32_t            flags1 = 0;
      uint32_t            reserved2 = 0;
      eosio::asset        reserved3;

      uint64_t primary_key()const { return owner.value; }

      enum class flags1_fields : uint32_t {
         ram_managed = 1,
         net_managed = 2,
         cpu_managed = 4
      };

      // explicit serialization macro is not necessary, used here only to improve compilation time
      EOSLIB_SERIALIZE( voter_info, (owner)(proxy)(producers)(staked)(unpaid_voteshare)(unpaid_voteshare_last_updated)(unpaid_voteshare_change_rate)
                                    (last_claim_time)(last_vote_weight)(proxied_vote_weight)(is_proxy)(flags1)(reserved2)(reserved3) )
   };

   struct [[eosio::table, eosio::contract("eosio.system")]] wps_voter {
       name owner;
       std::vector<name> proposals; /// the proposals approved by this voter if no proxy is set
       double last_vote_weight = 0;

       uint64_t primary_key()const { return owner.value; }

       EOSLIB_SERIALIZE( wps_voter, (owner)(proposals)(last_vote_weight))
   };


    struct [[eosio::table, eosio::contract("eosio.system")]] proposer {
        name account;
        string first_name;
        string last_name;
        string img_url;
        string bio;
        string country;
        string telegram;
        string website;
        string linkedin;
        time_point_sec last_claim_time;
        uint64_t primary_key() const { return account.value; }
        EOSLIB_SERIALIZE( proposer, (account)(first_name)(last_name)(img_url)(bio)(country)(telegram)(website)(linkedin)(last_claim_time) )
    };

    struct PROPOSAL_STATUS {
        const static uint8_t PENDING = 1;
        const static uint8_t REJECTED = 2;
        const static uint8_t ON_VOTE = 3;
        const static uint8_t FINISHED_VOTING = 4;
        const static uint8_t APPROVED = 5;       // approve
        const static uint8_t COMPLETED = 6;
    };

    struct [[eosio::table, eosio::contract("eosio.system")]] proposal {
        name proposer;        // proposer
        uint64_t id;
        name committee;       // committee
        string category;              // category
        uint16_t subcategory;         // subcategory
        string title;                 // title
        string summary;               // summary
        string project_img_url;       // project image or video url
        string description;           // overview
        string roadmap;               // roadmap
        uint64_t duration;            // duration
        vector<string> members;       // linkedin
        asset funding_goal;           // amount of EOS
        double total_votes;         // total votes
        uint8_t status;               // status
        time_point_sec vote_start_time;     // time when voting starts (seconds)
        time_point_sec fund_start_time;     // time when funding starts (seconds)
        uint32_t iteration_of_funding; // current number of iterations
        uint32_t total_iterations; // total number of iterations
        uint64_t primary_key() const { return proposer.value; }
        uint64_t by_id() const { return id; }
        double   by_votes()const    { return total_votes;  }
        EOSLIB_SERIALIZE( proposal, (proposer)(id)(committee)(category)(subcategory)(title)(summary)(project_img_url)(description)(roadmap)(duration)(members)(funding_goal)
                (total_votes)(status)(vote_start_time)(fund_start_time)(iteration_of_funding)(total_iterations) )
    };

    struct [[eosio::table, eosio::contract("eosio.system")]] committee {
        name committeeman;
        string category;
        bool is_oversight;
        uint64_t primary_key() const { return committeeman.value; }
        EOSLIB_SERIALIZE( committee, (committeeman)(category)(is_oversight) );
    };

    struct [[eosio::table, eosio::contract("eosio.system")]] reviewer {
        name account;
        name committee;
        string first_name;
        string last_name;
        uint64_t primary_key() const { return account.value; }
        EOSLIB_SERIALIZE( reviewer, (account)(committee)(first_name)(last_name) )
    };

    struct [[eosio::table("wpsglobal"), eosio::contract("eosio.system")]] wpsenv {
        uint32_t total_voting_percent = 5;           // 5%
        uint32_t duration_of_voting = 30;            // voting duration (days)
        uint32_t max_duration_of_funding = 500;      // funding duration (days)
        uint32_t total_iteration_of_funding = 6;     //
        uint64_t primary_key() const { return 0; }
        EOSLIB_SERIALIZE( wpsenv, (total_voting_percent)(duration_of_voting)(max_duration_of_funding)(total_iteration_of_funding) )
    };

    /**
     * Defines new global state parameters needed for wps in particular
     */
    struct [[eosio::table("wpsstate"), eosio::contract("eosio.system")]] wps_global_state {
        double total_stake = 0;
        EOSLIB_SERIALIZE( wps_global_state, (total_stake) )
    };

    /**
    * Proposers table
    *
    * @details The proposers table stores all WPS proposers' information
    */
    typedef eosio::multi_index<"proposers"_n, proposer> proposer_table;


    /**
    * Proposals table
    *
    * @details The proposals table stores all WPS proposal items
    */
    typedef eosio::multi_index< "proposals"_n, proposal,
            indexed_by< "idx"_n, const_mem_fun<proposal, uint64_t, &proposal::by_id>  >,
            indexed_by<"prototalvote"_n, const_mem_fun<proposal, double, &proposal::by_votes>  >
    > proposal_table;

    /**
    * Committees table
    *
    * @details The committees table stores all WPS committee accounts' information
    */
    typedef eosio::multi_index< "committees"_n, committee> committee_table;

    /**
    * Reviewers table
    *
    * @details The reviewers table stores all WPS reviewer accounts' information
    */
    typedef eosio::multi_index< "reviewers"_n, reviewer> reviewer_table;

    /**
    * WPS environment singleton
    *
    * @details The WPS environment singleton holds configurable variables for the system
    */
    typedef eosio::singleton< "wpsglobal"_n, wpsenv > wps_env_singleton;

    /**
     * Global wps state singleton
     */
    typedef eosio::singleton< "wpsstate"_n, wps_global_state > wps_global_state_singleton;

   /**
    * Producer reward information  
    */
   struct [[eosio::table, eosio::contract("eosio.system")]] reward_info {
      // A unique name is needed in order to avoid problems with ABI generator
      // which doesn't understand scopes (see eosio_global_reward)
      struct reward_info_counter_type {
         // producer's own rewards tracking
         uint64_t unpaid_blocks = 0;  // # of blocks produced

         void reset_rewards() {
           unpaid_blocks = 0;
         }

         // performance tracking
         double avg_blocks = 0.0;
         uint32_t samples = 0;
         uint32_t last_slot = 0;

         void update_performance(uint32_t produced_blocks, uint32_t expected_blocks, uint32_t current_slot, uint32_t blocks_performance_window) {
           expected_blocks = std::min(expected_blocks, blocks_performance_window);
           produced_blocks = std::min(expected_blocks, produced_blocks);  // Shouldn't really happen. If it does then blocks_performance_window is too low
           samples = std::min(samples + expected_blocks, blocks_performance_window);
           if(samples == 0) {
             // We don't want to crash the main loop, but this should never happen
             return;
           }
           avg_blocks = (produced_blocks + avg_blocks * (samples - expected_blocks)) / samples;
           last_slot = current_slot;
         }

         void reset_performance() {
           avg_blocks = 0;
           samples = 0;
         }
      };

      name                                         owner;
      uint32_t                                     current_type = 0;
      std::map<uint32_t, reward_info_counter_type> counters; // [reward_type, counters]

      // Table helpers / accessors

      auto primary_key() const { 
         return owner.value; 
      }

      void init(const name& owner) {
         this->owner = owner;
         current_type = enum_cast(reward_type::none);
         counters.try_emplace(enum_cast(reward_type::none), reward_info_counter_type());
         counters.try_emplace(enum_cast(reward_type::producer), reward_info_counter_type());
         counters.try_emplace(enum_cast(reward_type::standby), reward_info_counter_type());
      }

      void set_current_type(uint32_t rhs) { // raw uint32 type
         current_type = rhs;
      }

      void set_current_type(reward_type rhs) {
         set_current_type(enum_cast(rhs));
      }

      auto get_current_type() const {
         return static_cast<reward_type>(current_type);
      }

      const auto& get_counters(reward_type type) const {
         auto it = counters.find(enum_cast(type));
         check(it != counters.end(), "Cannot find counter data");
         return it->second;
      }

      auto& get_counters(reward_type type) {
         auto it = counters.find(enum_cast(type));
         check(it != counters.end(), "Cannot find counter data");
         return it->second;
      }

      void reset_rewards_counters() {
         for (auto& counter: counters)
            counter.second.reset_rewards();
      }

      auto& get_current_counter() {
         auto it = counters.find(current_type);
         check(it != counters.end(), "Cannot find counter data");
         return it->second;
      }

      void missed_blocks(uint32_t num_blocks, uint32_t current_slot, uint32_t blocks_performance_window) {
        auto &counter = get_current_counter();
        counter.update_performance(0, num_blocks, current_slot, blocks_performance_window);
      }

      void track_block(uint32_t current_slot, uint32_t blocks_performance_window) {
        auto &counter = get_current_counter();
        counter.update_performance(1, 1, current_slot, blocks_performance_window);
        counter.unpaid_blocks++;
      }

      optional<double> get_performance(reward_type as_type) {
        const auto &counter = get_counters(as_type);
        switch(as_type) {
          case reward_type::standby:
          case reward_type::producer:
            return counter.avg_blocks;
          default:
            return std::nullopt;
        }
      }

      // explicit serialization macro is not necessary, used here only to improve compilation time
      EOSLIB_SERIALIZE( reward_info, (owner)(current_type)(counters) )
   };


   /**
    * Voters table
    *
    * @details The voters table stores all the `voter_info`s instances, all voters information.
    */
   typedef eosio::multi_index< "voters"_n, voter_info >  voters_table;

    /**
     * WPS voters table
     *
     * @details The WPS voters table stores all the `wps_voter`s instances, all WPS voters information.
     */
    typedef eosio::multi_index< "wpsvoters"_n, wps_voter >  wps_voters_table;

   /**
    * Defines producer info table added in version 1.0
    */
   typedef eosio::multi_index< "producers"_n, producer_info,
                               indexed_by<"prototalvote"_n, const_mem_fun<producer_info, double, &producer_info::by_votes>  >
                             > producers_table;
   /**
    * Defines new producer info table added in version 1.3.0
    */
   typedef eosio::multi_index< "producers2"_n, producer_info2 > producers_table2;

   /**
    * Keeps produced blocks for rewards
    */
   typedef eosio::multi_index< "rewards"_n, reward_info > rewards_table;

   /**
    * Global state singleton added in version 1.0
    */
   typedef eosio::singleton< "global"_n, eosio_global_state >   global_state_singleton;
   
   /**
    * Global state singleton added in version 1.1.0
    */
   typedef eosio::singleton< "global2"_n, eosio_global_state2 > global_state2_singleton;
   
   /**
    * Global state singleton added in version 1.3
    */
   typedef eosio::singleton< "global3"_n, eosio_global_state3 > global_state3_singleton;

   /**
    * Global rewards singleton
    */
   typedef eosio::singleton< "glbreward"_n, eosio_global_reward > global_reward_singleton;

   struct [[eosio::table, eosio::contract("eosio.system")]] user_resources {
      name          owner;
      asset         net_weight;
      asset         cpu_weight;
      int64_t       ram_bytes = 0;

      bool is_empty()const { return net_weight.amount == 0 && cpu_weight.amount == 0 && ram_bytes == 0; }
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

      bool is_empty()const { return net_weight.amount == 0 && cpu_weight.amount == 0; }
      uint64_t  primary_key()const { return to.value; }

      // explicit serialization macro is not necessary, used here only to improve compilation time
      EOSLIB_SERIALIZE( delegated_bandwidth, (from)(to)(net_weight)(cpu_weight) )

   };

   struct [[eosio::table, eosio::contract("eosio.system")]] refund_request {
      name            owner;
      time_point_sec  request_time;
      eosio::asset    net_amount;
      eosio::asset    cpu_amount;

      bool is_empty()const { return net_amount.amount == 0 && cpu_amount.amount == 0; }
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
    * The EOSIO system contract.
    *
    * @details The EOSIO system contract governs ram market, voters, producers, global state.
    */
   class [[eosio::contract("eosio.system")]] system_contract : public native {

      private:
         voters_table            _voters;
         wps_voters_table        _wpsvoters;
         producers_table         _producers;
         rewards_table           _rewards;
         global_state_singleton  _global;
         global_state2_singleton _global2;
         global_reward_singleton _globalreward;
         eosio_global_state      _gstate;
         eosio_global_state2     _gstate2;
         eosio_global_reward     _greward;
         rammarket               _rammarket;
         proposer_table          _proposers;
         proposal_table          _proposals;
         committee_table         _committees;
         reviewer_table          _reviewers;
         wps_global_state_singleton _wps_global;
         wps_global_state        _wps_state;

      public:
         static constexpr eosio::name active_permission{"active"_n};
         static constexpr eosio::name token_account{"eosio.token"_n};
         static constexpr eosio::name ram_account{"eosio.ram"_n};
         static constexpr eosio::name ramfee_account{"eosio.ramfee"_n};
         static constexpr eosio::name stake_account{"eosio.stake"_n};
         static constexpr eosio::name bpay_account{"eosio.bpay"_n};
         static constexpr eosio::name spay_account{"eosio.spay"_n};
         static constexpr eosio::name vpay_account{"eosio.vpay"_n};
         static constexpr eosio::name names_account{"eosio.names"_n};
         static constexpr eosio::name saving_account{"eosio.saving"_n};
         static constexpr eosio::name voters_account{"eosio.voters"_n};
         static constexpr eosio::name genesis_account{"genesis.wax"_n};
         static constexpr eosio::name null_account{"eosio.null"_n};
         static constexpr symbol ramcore_symbol = symbol(symbol_code("RAMCORE"), 4);
         static constexpr symbol ram_symbol     = symbol(symbol_code("RAM"), 0);

         /**
          * System contract constructor.
          *
          * @details Constructs a system contract based on self account, code account and data.
          *
          * @param s    - The current code account that is executing the action,
          * @param code - The original code account that executed the action,
          * @param ds   - The contract data represented as an `eosio::datastream`.
          */
         system_contract( name s, name code, datastream<const char*> ds );
         ~system_contract();

         /**
          * Returns the core symbol by system account name
          *
          * @param system_account - the system account to get the core symbol for.
          */
         static symbol get_core_symbol( name system_account = "eosio"_n ) {
            rammarket rm(system_account, system_account.value);
            const static auto sym = get_core_symbol( rm );
            return sym;
         }

         // Actions:
         /**
          * Init action.
          *
          * @details Init action initializes the system contract for a version and a symbol.
          * Only succeeds when:
          * - version is 0 and
          * - symbol is found and
          * - system token supply is greater than 0,
          * - and system contract wasn’t already been initialized.
          *
          * @param version - the version, has to be 0,
          * @param core - the system symbol.
          */
         [[eosio::action]]
         void init( unsigned_int version, const symbol& core );

         /**
          * On block action.
          *
          * @details This special action is triggered when a block is applied by the given producer
          * and cannot be generated from any other source. It is used to pay producers and calculate
          * missed blocks of other producers. Producer pay is deposited into the producer's stake
          * balance and can be withdrawn over time. If blocknum is the start of a new round this may
          * update the active producer config from the producer votes.
          *
          * @param header - the block header produced.
          */
         [[eosio::action]]
         void onblock( ignore<block_header> header );

         /**
          * Set account limits action.
          *
          * @details Set the resource limits of an account
          *
          * @param account - name of the account whose resource limit to be set,
          * @param ram_bytes - ram limit in absolute bytes,
          * @param net_weight - fractionally proportionate net limit of available resources based on (weight / total_weight_of_all_accounts),
          * @param cpu_weight - fractionally proportionate cpu limit of available resources based on (weight / total_weight_of_all_accounts).
          */
         [[eosio::action]]
         void setalimits( const name& account, int64_t ram_bytes, int64_t net_weight, int64_t cpu_weight );

         /**
          * Set account RAM limits action.
          *
          * @details Set the RAM limits of an account
          *
          * @param account - name of the account whose resource limit to be set,
          * @param ram_bytes - ram limit in absolute bytes.
          */
         [[eosio::action]]
         void setacctram( const name& account, const std::optional<int64_t>& ram_bytes );

         /**
          * Set account NET limits action.
          *
          * @details Set the NET limits of an account
          *
          * @param account - name of the account whose resource limit to be set,
          * @param net_weight - fractionally proportionate net limit of available resources based on (weight / total_weight_of_all_accounts).
          */
         [[eosio::action]]
         void setacctnet( const name& account, const std::optional<int64_t>& net_weight );

         /**
          * Set account CPU limits action.
          *
          * @details Set the CPU limits of an account
          *
          * @param account - name of the account whose resource limit to be set,
          * @param cpu_weight - fractionally proportionate cpu limit of available resources based on (weight / total_weight_of_all_accounts).
          */
         [[eosio::action]]
         void setacctcpu( const name& account, const std::optional<int64_t>& cpu_weight );


         /**
          * Activates a protocol feature.
          *
          * @details Activates a protocol feature
          *
          * @param feature_digest - hash of the protocol feature to activate.
          */
         [[eosio::action]]
         void activate( const eosio::checksum256& feature_digest );

         /**
          * Activates producer/standby rewards
          *
          * @details 
          *   
          */
         [[eosio::action]]
         void activaterewd();

         /**
          * Configures producer/standby rewards
          *
          * @details
          *
          */
         [[eosio::action]]
         void setrwrdsenv(uint32_t producer_blocks_performance_window, uint32_t standby_blocks_performance_window, bool random_standby_selection);

         // functions defined in delegate_bandwidth.cpp

         /**
          * Delegate bandwidth and/or cpu action.
          *
          * @details Stakes SYS from the balance of `from` for the benefit of `receiver`.
          *
          * @param from - the account to delegate bandwidth from, that is, the account holding
          *    tokens to be staked,
          * @param receiver - the account to delegate bandwith to, that is, the account to
          *    whose resources staked tokens are added
          * @param stake_net_quantity - tokens staked for NET bandwidth,
          * @param stake_cpu_quantity - tokens staked for CPU bandwidth,
          * @param transfer - if true, ownership of staked tokens is transfered to `receiver`.
          *
          * @post All producers `from` account has voted for will have their votes updated immediately.
          */
         [[eosio::action]]
         void delegatebw( const name& from, const name& receiver,
                          const asset& stake_net_quantity, const asset& stake_cpu_quantity, bool transfer );

         /**
          * Undelegate bandwitdh action.
          *
          * @details Decreases the total tokens delegated by `from` to `receiver` and/or
          * frees the memory associated with the delegation if there is nothing
          * left to delegate.
          * This will cause an immediate reduction in net/cpu bandwidth of the
          * receiver.
          * A transaction is scheduled to send the tokens back to `from` after
          * the staking period has passed. If existing transaction is scheduled, it
          * will be canceled and a new transaction issued that has the combined
          * undelegated amount.
          * The `from` account loses voting power as a result of this call and
          * all producer tallies are updated.
          *
          * @param from - the account to undelegate bandwidth from, that is,
          *    the account whose tokens will be unstaked,
          * @param receiver - the account to undelegate bandwith to, that is,
          *    the account to whose benefit tokens have been staked,
          * @param unstake_net_quantity - tokens to be unstaked from NET bandwidth,
          * @param unstake_cpu_quantity - tokens to be unstaked from CPU bandwidth,
          *
          * @post Unstaked tokens are transferred to `from` liquid balance via a
          *    deferred transaction with a delay of 3 days.
          * @post If called during the delay period of a previous `undelegatebw`
          *    action, pending action is canceled and timer is reset.
          * @post All producers `from` account has voted for will have their votes updated immediately.
          * @post Bandwidth and storage for the deferred transaction are billed to `from`.
          */
         [[eosio::action]]
         void undelegatebw( const name& from, const name& receiver,
                            const asset& unstake_net_quantity, const asset& unstake_cpu_quantity );

         /**
          * Locks tokens on initial period for future rewards.
          */
         [[eosio::action]]
         void awardgenesis( name receiver,
                            const asset tokens, uint64_t nonce );
         
         /**
          * Reverts an awardgenesis action
          */
         [[eosio::action]]
         void delgenesis( uint64_t nonce );
 
         /**
          * Removing the amount of tokens from account's refunds
          */
         [[eosio::action]]
         void removerefund( name account, asset tokens );
         
         /**
          * Pays all awarded tokens for period since last claim
          */
         [[eosio::action]]
         void claimgenesis( name claimer);

         /**
          * Buy ram action.
          *
          * @details Increases receiver's ram quota based upon current price and quantity of
          * tokens provided. An inline transfer from receiver to system contract of
          * tokens will be executed.
          *
          * @param payer - the ram buyer,
          * @param receiver - the ram receiver,
          * @param quant - the quntity of tokens to buy ram with.
          */
         [[eosio::action]]
         void buyram( const name& payer, const name& receiver, const asset& quant );

         /**
          * Buy a specific amount of ram bytes action.
          *
          * @details Increases receiver's ram in quantity of bytes provided.
          * An inline transfer from receiver to system contract of tokens will be executed.
          *
          * @param payer - the ram buyer,
          * @param receiver - the ram receiver,
          * @param bytes - the quntity of ram to buy specified in bytes.
          */
         [[eosio::action]]
         void buyrambytes( const name& payer, const name& receiver, uint32_t bytes );

         /**
          * Sell ram action.
          *
          * @details Reduces quota by bytes and then performs an inline transfer of tokens
          * to receiver based upon the average purchase price of the original quota.
          *
          * @param account - the ram seller account,
          * @param bytes - the amount of ram to sell in bytes.
          */
         [[eosio::action]]
         void sellram( const name& account, int64_t bytes );

         /**
          * Refund action.
          *
          * @details This action is called after the delegation-period to claim all pending
          * unstaked tokens belonging to owner.
          *
          * @param owner - the owner of the tokens claimed.
          */
         [[eosio::action]]
         void refund( const name& owner );

         // functions defined in voting.cpp

         /**
          * Register producer action.
          *
          * @details Register producer action, indicates that a particular account wishes to become a producer,
          * this action will create a `producer_config` and a `producer_info` object for `producer` scope
          * in producers tables.
          *
          * @param producer - account registering to be a producer candidate,
          * @param producer_key - the public key of the block producer, this is the key used by block producer to sign blocks,
          * @param url - the url of the block producer, normally the url of the block producer presentation website,
          * @param location - is the country code as defined in the ISO 3166, https://en.wikipedia.org/wiki/List_of_ISO_3166_country_codes
          *
          * @pre Producer is not already registered
          * @pre Producer to register is an account
          * @pre Authority of producer to register
          */
         [[eosio::action]]
         void regproducer( const name& producer, const public_key& producer_key, const std::string& url, uint16_t location );

         /**
          * Unregister producer action.
          *
          * @details Deactivate the block producer with account name `producer`.
          * @param producer - the block producer account to unregister.
          */
         [[eosio::action]]
         void unregprod( const name& producer );

         /**
          * Set ram action.
          *
          * @details Set the ram supply.
          * @param max_ram_size - the amount of ram supply to set.
          */
         [[eosio::action]]
         void setram( uint64_t max_ram_size );

         /**
          * Set ram rate action.

          * @details Sets the rate of increase of RAM in bytes per block. It is capped by the uint16_t to
          * a maximum rate of 3 TB per year. If update_ram_supply hasn't been called for the most recent block,
          * then new ram will be allocated at the old rate up to the present block before switching the rate.
          *
          * @param bytes_per_block - the amount of bytes per block increase to set.
          */
         [[eosio::action]]
         void setramrate( uint16_t bytes_per_block );

         /**
          * Vote producer action.
          *
          * @details Votes for a set of producers. This action updates the list of `producers` voted for,
          * for `voter` account. If voting for a `proxy`, the producer votes will not change until the
          * proxy updates their own vote. Voter can vote for a proxy __or__ a list of at most 30 producers.
          * Storage change is billed to `voter`.
          *
          * @param voter - the account to change the voted producers for,
          * @param proxy - the proxy to change the voted producers for,
          * @param producers - the list of producers to vote for, a maximum of 30 producers is allowed.
          *
          * @pre Producers must be sorted from lowest to highest and must be registered and active
          * @pre If proxy is set then no producers can be voted for
          * @pre If proxy is set then proxy account must exist and be registered as a proxy
          * @pre Every listed producer or proxy must have been previously registered
          * @pre Voter must authorize this action
          * @pre Voter must have previously staked some EOS for voting
          * @pre Voter->staked must be up to date
          *
          * @post Every producer previously voted for will have vote reduced by previous vote weight
          * @post Every producer newly voted for will have vote increased by new vote amount
          * @post Prior proxy will proxied_vote_weight decremented by previous vote weight
          * @post New proxy will proxied_vote_weight incremented by new vote weight
          */
         [[eosio::action]]
         void voteproducer( const name& voter, const name& proxy, const std::vector<name>& producers );

         /**
          * Register proxy action.
          *
          * @details Set `proxy` account as proxy.
          * An account marked as a proxy can vote with the weight of other accounts which
          * have selected it as a proxy. Other accounts must refresh their voteproducer to
          * update the proxy's weight.
          * Storage change is billed to `proxy`.
          *
          * @param rpoxy - the account registering as voter proxy (or unregistering),
          * @param isproxy - if true, proxy is registered; if false, proxy is unregistered.
          *
          * @pre Proxy must have something staked (existing row in voters table)
          * @pre New state must be different than current state
          */
         [[eosio::action]]
         void regproxy( const name& proxy, bool isproxy );

         /**
          * Set the blockchain parameters
          *
          * @details Set the blockchain parameters. By tunning these parameters a degree of
          * customization can be achieved.
          * @param params - New blockchain parameters to set.
          */
         [[eosio::action]]
         void setparams( const eosio::blockchain_parameters& params );

         /**
          * Voter claim rewards action.
          * 
          * @details Claim the rewards for a voter.
          * @param owner - voter account claiming its rewards.
          */
         [[eosio::action]]
         void voterclaim(const name owner);

         // functions defined in producer_pay.cpp
         /**
          * Claim rewards action.
          *
          * @details Claim block producing and vote rewards.
          * @param owner - producer account claiming per-block and per-vote rewards.
          */
         [[eosio::action]]
         void claimrewards( const name& owner );

         /**
          * Claim GBM vote reward.
          * 
          * @details Claims the GBM reward for a voter.
          * @param owner - voter account claiming the reward.
         */
         [[eosio::action]]
         void claimgbmvote(const name owner);


         /**
          * Reset producer performance stats.
          * 
          * @details Allows a producer to reset their performance metrics collected
          * while operating as a particular producer type. Cannot be called within the
          * performance window number of blocks, for the producer type, since the last
          * time the metrics were updated.
          * @param producer - producer account being reset.
          * @param producer_type - producer type index being reset. 1 == regular bp. 2 == standby
          */
         [[eosio::action]]
         void resetperf(const name producer, uint32_t producer_type);


         /**
          * Claim GBM producer reward.
          * 
          * @details Claims the GBM reward for a producer.
          * @param owner - producer account claiming the reward.
         */
         [[eosio::action]]
         void claimgbmprod( const name owner );

         /**
          * Set privilege status for an account.
          *
          * @details Allows to set privilege status for an account (turn it on/off).
          * @param account - the account to set the privileged status for.
          * @param is_priv - 0 for false, > 0 for true.
          */
         [[eosio::action]]
         void setpriv( const name& account, uint8_t is_priv );

         /**
          * Remove producer action.
          *
          * @details Deactivates a producer by name, if not found asserts.
          * @param producer - the producer account to deactivate.
          */
         [[eosio::action]]
         void rmvproducer( const name& producer );

         /**
          * Update revision action.
          *
          * @details Updates the current revision.
          * @param revision - it has to be incremented by 1 compared with current revision.
          *
          * @pre Current revision can not be higher than 254, and has to be smaller
          * than or equal 1 (“set upper bound to greatest revision supported in the code”).
          */
         [[eosio::action]]
         void updtrevision( uint8_t revision );

         /**
          * Bid name action.
          *
          * @details Allows an account `bidder` to place a bid for a name `newname`.
          * @param bidder - the account placing the bid,
          * @param newname - the name the bid is placed for,
          * @param bid - the amount of system tokens payed for the bid.
          *
          * @pre Bids can be placed only on top-level suffix,
          * @pre Non empty name,
          * @pre Names longer than 12 chars are not allowed,
          * @pre Names equal with 12 chars can be created without placing a bid,
          * @pre Bid has to be bigger than zero,
          * @pre Bid's symbol must be system token,
          * @pre Bidder account has to be different than current highest bidder,
          * @pre Bid must increase current bid by 10%,
          * @pre Auction must still be opened.
          */
         [[eosio::action]]
         void bidname( const name& bidder, const name& newname, const asset& bid );

         /**
          * Bid refund action.
          *
          * @details Allows the account `bidder` to get back the amount it bid so far on a `newname` name.
          *
          * @param bidder - the account that gets refunded,
          * @param newname - the name for which the bid was placed and now it gets refunded for.
          */
         [[eosio::action]]
         void bidrefund( const name& bidder, const name& newname );

         [[eosio::action]]
         void regproposer(name account, const string& first_name, const string& last_name,
                            const string& img_url, const string& bio, const string& country, const string& telegram,
                            const string& website, const string& linkedin);

       [[eosio::action]]
       void editproposer(name account, const string& first_name, const string& last_name,
                             const string& img_url, const string& bio, const string& country, const string& telegram,
                             const string& website, const string& linkedin);

       [[eosio::action]]
       void rmvproposer(name account);

       [[eosio::action]]
       void claimfunds(name account);

       [[eosio::action]]
       void regproposal(
                   name proposer,
                   name committee,
                   uint16_t subcategory,
                   const string& title,
                   const string& summary,
                   const string& project_img_url,
                   const string& description,
                   const string& roadmap,
                   uint64_t duration,
                   const vector<string>& members,
                   const asset& funding_goal,
                   uint32_t total_iterations
       );

       [[eosio::action]]
       void editproposal(
                   name proposer,
                   name committee,
                   uint16_t subcategory,
                   const string& title,
                   const string& summary,
                   const string& project_img_url,
                   const string& description,
                   const string& roadmap,
                   uint64_t duration,
                   const vector<string>& members,
                   const asset& funding_goal,
                   uint32_t total_iterations
       );

       [[eosio::action]]
       void regreviewer(name committee, name reviewer, const string& first_name, const string& last_name);

       [[eosio::action]]
       void editreviewer(name committee, name reviewer, const string& first_name, const string& last_name);

       [[eosio::action]]
       void rmvreviewer(name committee, name reviewer);

       [[eosio::action]]
       void acceptprop(name reviewer, name proposer);

       [[eosio::action]]
       void rejectprop(name reviewer, name proposer, const string& reason);

       [[eosio::action]]
       void approve(name reviewer, name proposer);

       [[eosio::action]]
       void rmvreject(name reviewer, name proposer);

       [[eosio::action]]
       void rmvcompleted(name reviewer, name proposer);

       [[eosio::action]]
       void cleanvotes(name reviewer, name proposer, uint64_t begin, uint64_t end);

       [[eosio::action]]
       void setwpsenv(uint32_t total_voting_percent, uint32_t duration_of_voting, uint32_t max_duration_of_funding, uint32_t total_iteration_of_funding);

       [[eosio::action]]
       void setwpsstate(double total_stake);

       [[eosio::action]]
       void regcommittee(name committeeman, const string& category, bool is_oversight);

       [[eosio::action]]
       void edcommittee(name committeeman, const string& category, bool is_oversight);

       [[eosio::action]]
       void rmvcommittee(name committeeman);

       [[eosio::action]]
       void rejectfund(name committeeman, name proposer, const string& reason);

       [[eosio::action]]
       void voteproposal(const name& voter_name, const std::vector<name>& proposals);

         using init_action = eosio::action_wrapper<"init"_n, &system_contract::init>;
         using setacctram_action = eosio::action_wrapper<"setacctram"_n, &system_contract::setacctram>;
         using setacctnet_action = eosio::action_wrapper<"setacctnet"_n, &system_contract::setacctnet>;
         using setacctcpu_action = eosio::action_wrapper<"setacctcpu"_n, &system_contract::setacctcpu>;
         using activate_action = eosio::action_wrapper<"activate"_n, &system_contract::activate>;
         using activaterewd_action = eosio::action_wrapper<"activaterewd"_n, &system_contract::activaterewd>;
         using delegatebw_action = eosio::action_wrapper<"delegatebw"_n, &system_contract::delegatebw>;
         using awardgenesis_action = eosio::action_wrapper<"awardgenesis"_n, &system_contract::awardgenesis>;
         using delgenesis_action = eosio::action_wrapper<"delgenesis"_n, &system_contract::delgenesis>;
         using removerefund_action = eosio::action_wrapper<"removerefund"_n, &system_contract::removerefund>;
         using claimgenesis_action = eosio::action_wrapper<"claimgenesis"_n, &system_contract::claimgenesis>;
         using undelegatebw_action = eosio::action_wrapper<"undelegatebw"_n, &system_contract::undelegatebw>;
         using buyram_action = eosio::action_wrapper<"buyram"_n, &system_contract::buyram>;
         using buyrambytes_action = eosio::action_wrapper<"buyrambytes"_n, &system_contract::buyrambytes>;
         using sellram_action = eosio::action_wrapper<"sellram"_n, &system_contract::sellram>;
         using refund_action = eosio::action_wrapper<"refund"_n, &system_contract::refund>;
         using regproducer_action = eosio::action_wrapper<"regproducer"_n, &system_contract::regproducer>;
         using unregprod_action = eosio::action_wrapper<"unregprod"_n, &system_contract::unregprod>;
         using setram_action = eosio::action_wrapper<"setram"_n, &system_contract::setram>;
         using setramrate_action = eosio::action_wrapper<"setramrate"_n, &system_contract::setramrate>;
         using voteproducer_action = eosio::action_wrapper<"voteproducer"_n, &system_contract::voteproducer>;
         using regproxy_action = eosio::action_wrapper<"regproxy"_n, &system_contract::regproxy>;
         using claimrewards_action = eosio::action_wrapper<"claimrewards"_n, &system_contract::claimrewards>;
         using rmvproducer_action = eosio::action_wrapper<"rmvproducer"_n, &system_contract::rmvproducer>;
         using updtrevision_action = eosio::action_wrapper<"updtrevision"_n, &system_contract::updtrevision>;
         using bidname_action = eosio::action_wrapper<"bidname"_n, &system_contract::bidname>;
         using bidrefund_action = eosio::action_wrapper<"bidrefund"_n, &system_contract::bidrefund>;
         using setpriv_action = eosio::action_wrapper<"setpriv"_n, &system_contract::setpriv>;
         using setalimits_action = eosio::action_wrapper<"setalimits"_n, &system_contract::setalimits>;
         using setparams_action = eosio::action_wrapper<"setparams"_n, &system_contract::setparams>;
       using regproposer_action = eosio::action_wrapper<"regproposer"_n, &system_contract::regproposer>;
       using editproposer_action = eosio::action_wrapper<"editproposer"_n, &system_contract::editproposer>;
       using rmvproposer_action = eosio::action_wrapper<"rmvproposer"_n, &system_contract::rmvproposer>;
       using regproposal_action = eosio::action_wrapper<"regproposal"_n, &system_contract::regproposal>;
       using editproposal_action = eosio::action_wrapper<"editproposal"_n, &system_contract::editproposal>;
       using claimfunds_action = eosio::action_wrapper<"claimfunds"_n, &system_contract::claimfunds>;
       using regreviewer_action = eosio::action_wrapper<"regreviewer"_n, &system_contract::regreviewer>;
       using editreviewer_action = eosio::action_wrapper<"editreviewer"_n, &system_contract::editreviewer>;
       using rmvreviewer_action = eosio::action_wrapper<"rmvreviewer"_n, &system_contract::rmvreviewer>;
       using acceptprop_action = eosio::action_wrapper<"acceptprop"_n, &system_contract::acceptprop>;
       using rejectprop_action = eosio::action_wrapper<"rejectprop"_n, &system_contract::rejectprop>;
       using approve_action = eosio::action_wrapper<"approve"_n, &system_contract::approve>;
       using regcommittee_action = eosio::action_wrapper<"regcommittee"_n, &system_contract::regcommittee>;
       using edcommittee_action = eosio::action_wrapper<"edcommittee"_n, &system_contract::edcommittee>;
       using rmvcommittee_action = eosio::action_wrapper<"rmvcommittee"_n, &system_contract::rmvcommittee>;
       using rmvreject_action = eosio::action_wrapper<"rmvreject"_n, &system_contract::rmvreject>;
       using rmvcompleted_action = eosio::action_wrapper<"rmvcompleted"_n, &system_contract::rmvcompleted>;
       using cleanvotes_action = eosio::action_wrapper<"cleanvotes"_n, &system_contract::cleanvotes>;
       using setwpsenv_action = eosio::action_wrapper<"setwpsenv"_n, &system_contract::setwpsenv>;
       using setwpsstate_action = eosio::action_wrapper<"setwpsstate"_n, &system_contract::setwpsstate>;
       using rejectfund_action = eosio::action_wrapper<"rejectfund"_n, &system_contract::rejectfund>;
       using voteproposal_action = eosio::action_wrapper<"voteproposal"_n, &system_contract::voteproposal>;

      private:
         // WAX specifics

         void claim_producer_rewards( const name owner, bool as_gbm );
         void send_genesis_token( name from, name receiver, const asset tokens, bool add_backward_rewards = false);
         int64_t get_unclaimed_gbm_balance( name claimer );
         int64_t collect_voter_reward(const name owner);
         void fill_buckets();

         // Implementation details:

         static symbol get_core_symbol( const rammarket& rm ) {
            auto itr = rm.find(ramcore_symbol.raw());
            check(itr != rm.end(), "system contract must first be initialized");
            return itr->quote.balance.symbol;
         }

         //defined in eosio.system.cpp
         static eosio_global_state get_default_parameters();
         symbol core_symbol()const;
         void update_ram_supply();

         //defined in wps.cpp
         void update_wps_votes( const name& voter, const std::vector<name>& proposals);

         // defined in delegate_bandwidth.cpp
         void changebw( name from, const name& receiver,
                        const asset& stake_net_quantity, const asset& stake_cpu_quantity, bool transfer );
         void change_genesis( name unstaker );
         bool has_genesis_balance( name owner );
         void update_voting_power( const name& voter, const asset& total_update );

         // defined in voting.cpp
         void update_voter_votepay_share(const voters_table::const_iterator& voter_itr, double old_producers_performance);

         // defined in voting.hpp
         void update_producer_reward_status(int64_t schedule_version);

         void update_elected_producers( const block_timestamp& timestamp, const eosio::checksum256& previous_block_hash);
         void update_votes( const name& voter, const name& proxy, const std::vector<name>& producers, bool voting );
         void propagate_weight_change( const voter_info& voter );

         void select_producers_into( uint64_t begin, uint64_t count, reward_type type, prod_vec_t& result );
         bool is_it_time_to_select_a_standby() const;
         double calculate_producers_performance( const voter_info& voter );
         void record_missed_blocks( uint32_t last_slot, uint32_t current_slot );

         template <auto system_contract::*...Ptrs>
         class registration {
            public:
               template <auto system_contract::*P, auto system_contract::*...Ps>
               struct for_each {
                  template <typename... Args>
                  static constexpr void call( system_contract* this_contract, Args&&... args )
                  {
                     std::invoke( P, this_contract, args... );
                     for_each<Ps...>::call( this_contract, std::forward<Args>(args)... );
                  }
               };
               template <auto system_contract::*P>
               struct for_each<P> {
                  template <typename... Args>
                  static constexpr void call( system_contract* this_contract, Args&&... args )
                  {
                     std::invoke( P, this_contract, std::forward<Args>(args)... );
                  }
               };

               template <typename... Args>
               constexpr void operator() ( Args&&... args )
               {
                  for_each<Ptrs...>::call( this_contract, std::forward<Args>(args)... );
               }

               system_contract* this_contract;
         };
   };

   double stake2vote( int64_t staked );

   /** @}*/ // end of @defgroup eosiosystem eosio.system
} /// eosiosystem
