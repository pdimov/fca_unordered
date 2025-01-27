#ifndef UNORDERED_HYBRID_HPP
#define UNORDERED_HYBRID_HPP

// Copyright 2022 Joaquin M Lopez Munoz
// Copyright 2022 Peter Dimov
// Distributed under the Boost Software License, Version 1.0.
// http://www.boost.org/LICENSE_1_0.txt)
 
#include <algorithm>
#include <boost/container_hash/hash.hpp>
#include <boost/iterator/iterator_facade.hpp>
#include <boost/core/allocator_access.hpp>
#include <functional>
#include <limits>
#include <memory>
#include <vector>

namespace unordered_hybrid_impl
{
    
struct prime_fmod_size
{
    constexpr static std::size_t sizes[] = {
      53ul,97ul,193ul,389ul,769ul,
      1543ul,3079ul,6151ul,12289ul,24593ul,
      49157ul,98317ul,196613ul,393241ul,786433ul,
      1572869ul,3145739ul,6291469ul,12582917ul,25165843ul,
      50331653ul,100663319ul,201326611ul,402653189ul,805306457ul, };

    constexpr static uint64_t inv_sizes[] = {
      348051774975651918ull,190172619316593316ull,95578984837873325ull,
      47420935922132524ull,23987963684927896ull,11955116055547344ull,
      5991147799191151ull,2998982941588287ull,1501077717772769ull,
      750081082979285ull,375261795343686ull,187625172388393ull,
      93822606204624ull,46909513691883ull,23456218233098ull,
      11728086747027ull,5864041509391ull,2932024948977ull,
      1466014921160ull,733007198436ull,366503839517ull,
      183251896093ull,91625960335ull,45812983922ull,22906489714ull,
    };

    static inline std::size_t size_index(std::size_t n)
    {
        const std::size_t* bound = std::lower_bound(
            std::begin(sizes), std::end(sizes), n);
        if (bound == std::end(sizes))--bound;
        return bound - sizes;
    }

    static inline std::size_t size(std::size_t size_index)
    {
        return sizes[size_index];
    }

    // https://github.com/lemire/fastmod

#ifdef _MSC_VER
    static inline uint64_t mul128_u32(uint64_t lowbits, uint32_t d)
    {
        return __umulh(lowbits, d);
    }
#else // _MSC_VER
    static inline uint64_t mul128_u32(uint64_t lowbits, uint32_t d)
    {
        return ((__uint128_t)lowbits * d) >> 64;
    }
#endif

    static inline uint32_t fastmod_u32(uint32_t a, uint64_t M, uint32_t d)
    {
        uint64_t lowbits = M * a;
        return (uint32_t)(mul128_u32(lowbits, d));
    }

    static inline std::size_t position(std::size_t hash, std::size_t size_index)
    {
        return fastmod_u32(
            uint32_t(hash) + uint32_t(hash >> 32),
            inv_sizes[size_index], uint32_t(sizes[size_index]));
    }
};

struct pow2_size
{
    static inline std::size_t size_index(std::size_t n)
    {
        return n <= 32 ?
            5 :
            static_cast<std::size_t>(boost::core::bit_width(n - 1));
    }

    static inline std::size_t size(std::size_t size_index)
    {
        return std::size_t(1) << size_index;
    }

    static inline std::size_t position(std::size_t hash, std::size_t size_index)
    {
        return hash >> (sizeof(std::size_t) * 8 - size_index);
    }
};

struct pow2_fib_size: pow2_size
{
    static inline std::size_t mix_hash(std::size_t hash)
    {
        // https://en.wikipedia.org/wiki/Hash_function#Fibonacci_hashing
        const std::size_t m = 11400714819323198485ull;
        return hash * m;
    }

    static inline std::size_t position(std::size_t hash, std::size_t size_index)
    {
        return pow2_size::position(mix_hash(hash), size_index);
    }
};

template<class T, class A> struct node
{
    node* next_ = nullptr;
    std::size_t hash_ = 0;
    std::aligned_storage_t<sizeof(T), alignof(T)> storage_;

    node() = default;

    explicit node( T const& x, std::size_t hash )
    {
        ::new( &storage_ ) T( x );
        hash_ = hash * 2 + 1;
    }

    explicit node( T && x, std::size_t hash )
    {
        ::new( &storage_ ) T( std::move( x ) );
        hash_ = hash * 2 + 1;
    }

    ~node()
    {
        if( initialized() )
        {
            value().~T();
        }

        if( next_ != nullptr && next_ != (node*)-1 )
        {
            // delete next();

            using allocator_type = typename boost::allocator_rebind<A, node>::type;

            allocator_type a;

            boost::allocator_destroy( a, next_ );
            boost::allocator_deallocate( a, next_, 1 );
        }
    }

    node( node const& ) = delete;
    node& operator=( node const& ) = delete;

    node( node&& ) = delete;
    node& operator=( node&& ) = delete;

    void construct( T const& x, std::size_t hash )
    {
        BOOST_ASSERT( !initialized() );

        ::new( &storage_ ) T( x );
        hash_ = hash * 2 + 1;
    }

    void construct( T && x, std::size_t hash )
    {
        BOOST_ASSERT( !initialized() );

        ::new( &storage_ ) T( std::move( x ) );
        hash_ = hash * 2 + 1;
    }

    void destroy()
    {
        BOOST_ASSERT( initialized() );

        value().~T();
        hash_ = 0;
    }

    bool initialized() const noexcept
    {
        return ( hash_ & 1 ) != 0;
    }

    node* next() const noexcept
    {
        return next_;
    }

    T& value() noexcept
    {
        BOOST_ASSERT( initialized() );
        return *(T*)(&storage_);
    }

    T const& value() const noexcept
    {
        BOOST_ASSERT( initialized() );
        return *(T*)(&storage_);
    }

    bool empty() const noexcept
    {
        if( initialized() || next_ == (node*)-1 ) return false;

        if( next() == nullptr ) return true;

        return next()->empty();
    }
};

template<class T, class A> struct bucket_iterator: public boost::iterator_facade<bucket_iterator<T, A>, node<T, A>, boost::forward_traversal_tag>
{
private:

    using node_type = node<T, A>;

    node_type* p_ = nullptr;

public:

    bucket_iterator() = default;

private:

    friend class boost::iterator_core_access;
    template<class, class, class> friend class bucket_array;
    template<class, class, class, class, class> friend class unordered_hybrid_set;

    bucket_iterator( node_type* p ): p_( p ) {}

    auto& dereference() const noexcept { return *p_; }
    bool equal( bucket_iterator const & x) const noexcept { return p_ == x.p_; }

    void increment() noexcept
    {
        do
        {
            ++p_;
        }
        while( p_->empty() );
    }
};

template<class T, class Allocator, class SizePolicy> class bucket_array
{
private:

    using size_policy = SizePolicy;
    using node_type = node<T, Allocator>;

public:

    using value_type = node<T, Allocator>;
    using size_type = std::size_t;
    using allocator_type = typename boost::allocator_rebind<Allocator, node_type>::type;
    using iterator = bucket_iterator<T, Allocator>;

private:

    std::size_t size_index_, size_;
    std::vector<value_type, allocator_type> buckets;
    iterator begin_ = end();

public:

    bucket_array( size_type n, const Allocator& al ):
        size_index_( size_policy::size_index(n) ),
        size_( size_policy::size(size_index_) ),
        buckets( size_ + 1, al )
    {
        buckets.back().next_ = (node_type*)-1;
    }

    bucket_array( bucket_array&& ) = default;

    bucket_array& operator=( bucket_array&& r ) noexcept
    {
        size_index_ = r.size_index_;
        size_ = r.size_;
        begin_ = r.begin_;

        buckets.swap( r.buckets );

        return *this;
    }

    iterator begin() const { return begin_; }
    iterator end() const { return at(size_); }
    size_type capacity() const { return size_; }
    iterator at( size_type n ) const { return const_cast<value_type*>( &buckets[ n ] ); }

    size_type position( std::size_t hash ) const
    {
        return size_policy::position( hash, size_index_ );
    }

    template<class U> node_type* insert_node( iterator itb, U&& x, std::size_t hash )
    {
        node_type* p = itb.p_;

        BOOST_ASSERT( p->next_ != (node_type*)-1 );

        if( !p->initialized() )
        {
            p->construct( std::forward<U>( x ), hash );
        }
        else
        {
            // node_type* p2 = ::new node_type( std::forward<U>( x ), hash );

            allocator_type a;

            node_type * p2 = boost::allocator_allocate( a, 1 );

            try
            {
                boost::allocator_construct( a, p2, std::forward<U>( x ), hash );
            }
            catch( ... )
            {
                boost::allocator_deallocate( a, p2, 1 );
                throw;
            }

            p2->next_ = p->next_;
            p->next_ = p2;

            p = p2;
        }

        if( begin_.p_ > itb.p_ )
        {
            begin_ = itb;
        }

        return p;
    }

    void delete_node( iterator itb, node_type* p ) noexcept
    {
        BOOST_ASSERT( p->initialized() );

        p->destroy();

        for( ;; )
        {
            node_type* n = p->next();

            if( n == nullptr ) break;
            if( n->initialized() ) break;

            p->next_ = n->next_;
            n->next_ = 0;

            // delete n;

            allocator_type a;

            boost::allocator_destroy( a, n );
            boost::allocator_deallocate( a, n, 1 );
        }

        adjust_begin( itb );
    }

private:

    void adjust_begin( iterator itb )
    {
        if( begin_ == itb && begin_->empty() )
        {
            ++begin_;
        }
    }
};

template<class T, class Hash = boost::hash<T>, class Pred = std::equal_to<T>,
    class Allocator = std::allocator<T>, class SizePolicy = prime_fmod_size>
class unordered_hybrid_set
{
private:

    using node_type = node<T, Allocator>;

    using bucket_array_type = bucket_array<T, Allocator, SizePolicy>;
    using bucket_iterator = typename bucket_array_type::iterator;

public:

    using key_type = T;
    using value_type = T;
    using size_type = std::size_t;

private:

    Hash                h;
    Pred                pred;
    Allocator           al;
    float               mlf = 1.0f;
    size_type           size_ = 0;
    bucket_array_type   buckets{ 0, al };
    size_type           ml = max_load();

public:

    class const_iterator: public boost::iterator_facade<const_iterator, const value_type, boost::forward_traversal_tag>
    {
    public:

        const_iterator() = default;

    private:

        node_type* p_ = nullptr;
        bucket_iterator itb_ = {};

    private:

        friend class unordered_hybrid_set;
        friend class boost::iterator_core_access;

        const_iterator( node_type* p, bucket_iterator itb ): p_( p ), itb_( itb ) {}

        value_type const & dereference() const noexcept
        {
            return p_->value();
        }

        bool equal( const_iterator const & x ) const noexcept
        {
            return p_ == x.p_;
        }

        void increment() noexcept
        {
            BOOST_ASSERT( p_->initialized() );

            for( ;; )
            {
                node_type* n = p_->next();

                if( n == nullptr )
                {
                    ++itb_;
                    p_ = itb_.p_;
                }
                else
                {
                    p_ = n;
                }

                if( p_->initialized() || p_->next_ == (node_type*)-1 ) break;
            }
        }
    };

    using iterator = const_iterator;

    unordered_hybrid_set() = default;

    unordered_hybrid_set( std::size_t n, Allocator const& al ): al( al ), buckets( n, al )
    {
    }

    ~unordered_hybrid_set() = default;

    unordered_hybrid_set& operator=( unordered_hybrid_set&& ) = default;

    const_iterator begin() const noexcept
    {
        auto itb = buckets.begin();
        return { itb.p_, itb };
    }

    const_iterator end() const noexcept
    {
        auto itb = buckets.end();
        return { itb.p_, itb };
    }

    size_type size() const noexcept
    {
        return size_;
    }

    auto insert( T const & x )
    {
        return insert_impl(x);
    }
    
    auto insert( T&& x )
    {
        return insert_impl( std::move( x ) );
    }

    void erase( const_iterator pos )
    {
        buckets.delete_node( pos.itb_, pos.p_ );
        --size_;
    }

    template<class Key>
    size_type erase( Key const & x )
    {
        auto it = find( x );

        if( it == end() )
        {
            return 0;
        }

        erase( it );
        return 1;
    }

    template<class Key>
    iterator find( Key const & x ) const
    {
        std::size_t hash = h( x );
        return find( x, buckets.at( buckets.position( hash ) ), hash );
    }

private:

    template<class Value> std::pair<iterator, bool> insert_impl( Value&& x )
    {
        auto hash = h( x );
        auto itb = buckets.at( buckets.position( hash ) );

        auto it = find( x, itb, hash );

        if( it != end() )
        {
            return { it, false };
        }

        if( size_ + 1 > ml )
        {
            rehash( size_ + 1 );
            itb = buckets.at( buckets.position( hash ) );
        }

        auto p = buckets.insert_node( itb, std::forward<Value>( x ), hash );
        ++size_;

        return { { p, itb }, true };
    }

    void rehash( size_type n )
    {
        std::size_t bc = (std::numeric_limits<std::size_t>::max)();

        float fbc = 1.0f + static_cast<float>( n ) / mlf;

        if( bc > fbc )
        {
            bc = static_cast<std::size_t>( fbc );
        }

        unordered_hybrid_set newset( bc, al );

        for( auto& x: *this )
        {
            newset.insert( std::move( x ) );
        }

        *this = std::move( newset );
    }

    template<class Key>
    iterator find( Key const & x, bucket_iterator itb, std::size_t hash ) const
    {
        node_type * p = itb.p_;

        for( ;; )
        {
            if( p->hash_ == ( hash * 2 + 1 ) && pred( x, p->value() ) )
            {
                return { p, itb };
            }

            p = p->next();

            if( p == nullptr ) break;
        }

        return end();
    }

    size_type max_load() const
    {
        float fml = mlf * static_cast<float>( buckets.capacity() );

        auto res = (std::numeric_limits<size_type>::max)();

        if( res > fml )
        {
            res = static_cast<size_type>(fml);
        }

        return res;
    }
};

template<class Key,class Value>
struct map_value_adaptor
{
    Key first;
    mutable Value second;
};

template<typename Hash>
struct map_hash_adaptor
{
    template<typename T>
    auto operator()(const T& x)const
    {
        return h(x);
    }

    template<class Key, class Value>
    auto operator()(const map_value_adaptor<Key, Value>& x)const
    {
        return h(x.first);
    }

    Hash h;
};

template<typename Pred>
struct map_pred_adaptor
{
    template<typename T, class Key, class Value>
    auto operator()(
        const T& x, const map_value_adaptor<Key, Value>& y) const
    {
        return pred(x, y.first);
    }

    template<class Key, class Value, typename T>
    auto operator()(
        const map_value_adaptor<Key, Value>& x, const T& y) const
    {
        return pred(x.first, y);
    }

    template<class Key, class Value>
    auto operator()(
        const map_value_adaptor<Key, Value>& x,
        const map_value_adaptor<Key, Value>& y)const
    {
        return pred(x.first, y.first);
    }

    Pred pred;
};

template<class Key, class Value, class Hash = boost::hash<Key>, class Pred = std::equal_to<Key>,
    class Allocator = std::allocator<map_value_adaptor<Key,Value>>, class SizePolicy = prime_fmod_size
>
using unordered_hybrid_map = unordered_hybrid_set<
    map_value_adaptor<Key,Value>,
    map_hash_adaptor<Hash>, map_pred_adaptor<Pred>,
    Allocator, SizePolicy
>;

} // namespace unordered_hybrid_impl

using unordered_hybrid_impl::unordered_hybrid_set;
using unordered_hybrid_impl::unordered_hybrid_map;

#endif
