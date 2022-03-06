// Copyright 2021 Peter Dimov.
// Distributed under the Boost Software License, Version 1.0.
// https://www.boost.org/LICENSE_1_0.txt
//
// Modified by Joaquin M Lopez Munoz: added fca[_*]_unordered[_bucket]_map
// Copyright 2022 Joaquin M Lopez Munoz.
// Distributed under the Boost Software License, Version 1.0.
// https://www.boost.org/LICENSE_1_0.txt

#define _SILENCE_CXX17_OLD_ALLOCATOR_MEMBERS_DEPRECATION_WARNING

#include <boost/unordered_map.hpp>
#include <boost/multi_index_container.hpp>
#include <boost/multi_index/hashed_index.hpp>
#include <boost/multi_index/member.hpp>
#include <boost/core/detail/splitmix64.hpp>
#include <boost/config.hpp>
#include "fca_unordered.hpp"
#include "unordered_hybrid.hpp"
#ifdef HAVE_ABSEIL
# include "absl/container/node_hash_map.h"
# include "absl/container/flat_hash_map.h"
#endif
#include <unordered_map>
#include <map>
#include <cstdint>
#include <iostream>
#include <chrono>
#include <string_view>

using namespace std::chrono_literals;

static void print_time( std::chrono::steady_clock::time_point & t1, char const* label, std::uint32_t s, std::size_t size )
{
    auto t2 = std::chrono::steady_clock::now();

    std::cout << label << ": " << ( t2 - t1 ) / 1ms << " ms (s=" << s << ", size=" << size << ")\n";

    t1 = t2;
}

constexpr unsigned N = 2'000'000;
constexpr int K = 10;

static std::vector<std::string> indices1, indices2;

static std::string make_index( unsigned x )
{
    char buffer[ 64 ];
    std::snprintf( buffer, sizeof(buffer), "pfx_%u_sfx", x );

    return buffer;
}

static std::string make_random_index( unsigned x )
{
    char buffer[ 64 ];
    std::snprintf( buffer, sizeof(buffer), "pfx_%0*d_%u_sfx", x % 8 + 1, 0, x );

    return buffer;
}

static void init_indices()
{
    indices1.reserve( N*2+1 );
    indices1.push_back( make_index( 0 ) );

    for( unsigned i = 1; i <= N*2; ++i )
    {
        indices1.push_back( make_index( i ) );
    }

    indices2.reserve( N*2+1 );
    indices2.push_back( make_index( 0 ) );

    {
        boost::detail::splitmix64 rng;

        for( unsigned i = 1; i <= N*2; ++i )
        {
            indices2.push_back( make_random_index( static_cast<std::uint32_t>( rng() ) ) );
        }
    }
}

template<class Map> void BOOST_NOINLINE test_insert( Map& map, std::chrono::steady_clock::time_point & t1 )
{
    for( unsigned i = 1; i <= N; ++i )
    {
        map.insert( { indices1[ i ], i } );
    }

    print_time( t1, "Consecutive insert",  0, map.size() );

    for( unsigned i = 1; i <= N; ++i )
    {
        map.insert( { indices2[ i ], i } );
    }

    print_time( t1, "Random insert",  0, map.size() );

    std::cout << std::endl;
}

template<class Map> void BOOST_NOINLINE test_lookup( Map& map, std::chrono::steady_clock::time_point & t1 )
{
    std::uint32_t s;
    
    s = 0;

    for( int j = 0; j < K; ++j )
    {
        for( unsigned i = 1; i <= N * 2; ++i )
        {
            auto it = map.find( indices1[ i ] );
            if( it != map.end() ) s += it->second;
        }
    }

    print_time( t1, "Consecutive lookup",  s, map.size() );

    s = 0;

    for( int j = 0; j < K; ++j )
    {
        for( unsigned i = 1; i <= N * 2; ++i )
        {
            auto it = map.find( indices2[ i ] );
            if( it != map.end() ) s += it->second;
        }
    }

    print_time( t1, "Random lookup",  s, map.size() );

    std::cout << std::endl;
}

template<class Map> void BOOST_NOINLINE test_iteration( Map& map, std::chrono::steady_clock::time_point & t1 )
{
    auto it = map.begin();

    while( it != map.end() )
    {
        if( it->second & 1 )
        {
            map.erase( it++ );
        }
        else
        {
            ++it;
        }
    }

    print_time( t1, "Iterate and erase odd elements",  0, map.size() );

    std::cout << std::endl;
}

template<class Map> void BOOST_NOINLINE test_erase( Map& map, std::chrono::steady_clock::time_point & t1 )
{
    for( unsigned i = 1; i <= N; ++i )
    {
        map.erase( indices1[ i ] );
    }

    print_time( t1, "Consecutive erase",  0, map.size() );

    {
        boost::detail::splitmix64 rng;

        for( unsigned i = 1; i <= N; ++i )
        {
            map.erase( indices2[ i ] );
        }
    }

    print_time( t1, "Random erase",  0, map.size() );

    std::cout << std::endl;
}

static std::vector< std::pair<std::string, long long> > times;

template<template<class...> class Map> void BOOST_NOINLINE test( char const* label )
{
    std::cout << label << ":\n\n";

    Map<std::string_view, std::uint32_t> map;

    auto t0 = std::chrono::steady_clock::now();
    auto t1 = t0;

    test_insert( map, t1 );
    test_lookup( map, t1 );
    test_iteration( map, t1 );
    test_lookup( map, t1 );
    test_erase( map, t1 );

    auto tN = std::chrono::steady_clock::now();
    std::cout << "Total: " << ( tN - t0 ) / 1ms << " ms\n\n";

    times.push_back( { label, ( tN - t0 ) / 1ms } );
}

// multi_index emulation of unordered_map

template<class K, class V> struct pair
{
    K first;
    mutable V second;
};

using namespace boost::multi_index;

template<class K, class V> using multi_index_map = multi_index_container<
  pair<K, V>,
  indexed_by<
    hashed_unique< member<pair<K, V>, K, &pair<K, V>::first> >
  >
>;

// alternative size policies / bucket arrays for fca_unordered

template<class K, class V, class H=boost::hash<K>>
using fca_switch_unordered_map =
  fca_unordered_map<
    K, V, H,std::equal_to<K>,
    std::allocator<fca_unordered_impl::map_value_adaptor<K, V>>,
    fca_unordered_impl::prime_switch_size>;

template<class K, class V, class H=boost::hash<K>>
using fca_fmod_unordered_map =
  fca_unordered_map<
    K, V, H,std::equal_to<K>,
    std::allocator<fca_unordered_impl::map_value_adaptor<K, V>>,
    fca_unordered_impl::prime_fmod_size>;

template<class K, class V, class H=boost::hash<K>>
using fca_pow2_unordered_map =
  fca_unordered_map<
    K, V, H,std::equal_to<K>,
    std::allocator<fca_unordered_impl::map_value_adaptor<K, V>>,
    fca_unordered_impl::pow2_size>;

template<class K, class V, class H=boost::hash<K>>
using fca_pow2_fib_unordered_map =
  fca_unordered_map<
    K, V, H,std::equal_to<K>,
    std::allocator<fca_unordered_impl::map_value_adaptor<K, V>>,
    fca_unordered_impl::pow2_fib_size>;

template<class K, class V, class H=boost::hash<K>>
using fca_fmod_unordered_bucket_map =
  fca_unordered_map<
    K, V, H,std::equal_to<K>,
    std::allocator<fca_unordered_impl::map_value_adaptor<K, V>>,
    fca_unordered_impl::prime_fmod_size,
    fca_unordered_impl::simple_buckets>;

// fnv1a_hash

template<int Bits> struct fnv1a_hash_impl;

template<> struct fnv1a_hash_impl<32>
{
    std::size_t operator()( std::string_view const& s ) const
    {
        std::size_t h = 0x811C9DC5u;

        char const * first = s.data();
        char const * last = first + s.size();

        for( ; first != last; ++first )
        {
            h ^= static_cast<unsigned char>( *first );
            h *= 0x01000193ul;
        }

        return h;
    }
};

template<> struct fnv1a_hash_impl<64>
{
    std::size_t operator()( std::string_view const& s ) const
    {
        std::size_t h = 0xCBF29CE484222325ull;

        char const * first = s.data();
        char const * last = first + s.size();

        for( ; first != last; ++first )
        {
            h ^= static_cast<unsigned char>( *first );
            h *= 0x00000100000001B3ull;
        }

        return h;
    }
};

struct fnv1a_hash: fnv1a_hash_impl< std::numeric_limits<std::size_t>::digits > {};

template<class K, class V> using std_unordered_map_fnv1a =
    std::unordered_map<K, V, fnv1a_hash>;

template<class K, class V> using boost_unordered_map_fnv1a =
    boost::unordered_map<K, V, fnv1a_hash>;

template<class K, class V> using multi_index_map_fnv1a = multi_index_container<
  pair<K, V>,
  indexed_by<
    hashed_unique< member<pair<K, V>, K, &pair<K, V>::first>, fnv1a_hash >
  >
>;

template<class K, class V> using fca_unordered_map_fnv1a =
  fca_unordered_map<K, V, fnv1a_hash>;

template<class K, class V> using fca_switch_unordered_map_fnv1a =
  fca_switch_unordered_map<K, V, fnv1a_hash>;

template<class K, class V> using fca_fmod_unordered_map_fnv1a =
  fca_fmod_unordered_map<K, V, fnv1a_hash>;

template<class K, class V> using fca_pow2_unordered_map_fnv1a =
  fca_pow2_unordered_map<K, V, fnv1a_hash>;

template<class K, class V> using fca_pow2_fib_unordered_map_fnv1a =
  fca_pow2_fib_unordered_map<K, V, fnv1a_hash>;

template<class K, class V> using fca_fmod_unordered_bucket_map_fnv1a =
  fca_fmod_unordered_bucket_map<K, V, fnv1a_hash>;

template<class K, class V> using unordered_hybrid_map_fnv1a =
  unordered_hybrid_map<K, V, fnv1a_hash>;

#ifdef HAVE_ABSEIL

template<class K, class V> using absl_node_hash_map_fnv1a =
    absl::node_hash_map<K, V, fnv1a_hash>;

template<class K, class V> using absl_flat_hash_map_fnv1a =
    absl::flat_hash_map<K, V, fnv1a_hash>;

#endif
//

int main()
{
    init_indices();
    
    test<std_unordered_map_fnv1a>( "std::unordered_map, FNV-1a" );
    test<boost_unordered_map_fnv1a>( "boost::unordered_map, FNV-1a" );
    test<multi_index_map_fnv1a>( "multi_index_map, FNV-1a" );

    test<fca_unordered_map_fnv1a>( "fca_unordered_map, FNV-1a" );
    test<fca_pow2_fib_unordered_map_fnv1a>( "fca_pow2_fib_unordered_map, FNV-1a" );
    test<fca_fmod_unordered_map_fnv1a>( "fca_fmod_unordered_map, FNV-1a" );
    test<fca_fmod_unordered_bucket_map_fnv1a>( "fca_fmod_unordered_bucket_map, FNV-1a" );

    test<unordered_hybrid_map_fnv1a>( "unordered_hybrid_map, FNV-1a" );

#ifdef HAVE_ABSEIL

    test<absl_node_hash_map_fnv1a>( "absl::node_hash_map, FNV-1a" );
    test<absl_flat_hash_map_fnv1a>( "absl::flat_hash_map, FNV-1a" );

#endif

    std::cout << "---\n\n";

    for( auto const& x: times )
    {
        std::cout << x.first << ": " << x.second << " ms\n";
    }
}

#ifdef HAVE_ABSEIL
# include "absl/container/internal/raw_hash_set.cc"
# include "absl/hash/internal/hash.cc"
# include "absl/hash/internal/low_level_hash.cc"
# include "absl/hash/internal/city.cc"
#endif
