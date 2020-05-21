#include <iostream>
#include <iomanip>
#include <sstream>
#include <vector>
#include <string>
#include <set>
#include <unordered_set>
#include <map>
#include <unordered_map>
#include <stack>
#include <queue>
#include <deque>
#include <algorithm>
#include <functional>
#include <iterator>
#include <limits>
#include <numeric>
#include <utility>
#include <type_traits>
#include <cmath>
#include <cassert>
#include <cstdio>

using namespace std;
using namespace placeholders;

using LL = long long;
using ULL = unsigned long long;
using VI = vector< int >;
using VVI = vector< vector< int > >;
using VS = vector< string >;
using ISS = istringstream;
using OSS = ostringstream;
using PII = pair< int, int >;
using VPII = vector< pair< int, int > >;
template < typename T = int > using VT = vector< T >;
template < typename T = int > using VVT = vector< vector< T > >;
template < typename T = int > using LIM = numeric_limits< T >;
template < typename T = int > using OSI = ostream_iterator< T >;

template < typename T > inline istream& operator>>( istream &s, vector< T > &v ){ for ( T &t : v ) { s >> t; } return s; }
template < typename T > inline ostream& operator<<( ostream &s, const vector< T > &v ){ for ( int i = 0; i < int( v.size() ); ++i ){ s << ( " " + !i ) << v[i]; } return s; }

void in_impl(){};
template < typename T, typename... TS > void in_impl( T &head, TS &... tail ){ cin >> head; in_impl( tail ... ); }
#define IN( T, ... ) T __VA_ARGS__; in_impl( __VA_ARGS__ );

template < typename T > inline T fromString( const string &s ) { T res; istringstream iss( s ); iss >> res; return res; }
template < typename T > inline string toString( const T &a ) { ostringstream oss; oss << a; return oss.str(); }

#define NUMBERED( name, number ) NUMBERED2( name, number )
#define NUMBERED2( name, number ) name ## _ ## number
#define REP1( n ) REP2( NUMBERED( REP_COUNTER, __LINE__ ), n )
#define REP2( i, n ) REP3( i, 0, n )
#define REP3( i, m, n ) for ( int i = ( int )( m ); i < ( int )( n ); ++i )
#define GET_REP( a, b, c, F, ... ) F
#define REP( ... ) GET_REP( __VA_ARGS__, REP3, REP2, REP1 )( __VA_ARGS__ )
#define FOR( e, c ) for ( auto &&e : c )
#define ALL( c ) begin( c ), end( c )
#define AALL( a ) ( remove_all_extents< decltype( a ) >::type * )a, ( remove_all_extents< decltype( a ) >::type * )a + sizeof( a ) / sizeof( remove_all_extents< decltype( a ) >::type )

#define SZ( v ) ( (int)( v ).size() )
#define EXISTS( c, e ) ( ( c ).find( e ) != ( c ).end() )

template < typename T > inline bool chmin( T &a, const T &b ){ if ( b < a ) { a = b; return true; } return false; }
template < typename T > inline bool chmax( T &a, const T &b ){ if ( a < b ) { a = b; return true; } return false; }

#define PB push_back
#define EM emplace
#define EB emplace_back
#define BI back_inserter

#define MP make_pair
#define fst first
#define snd second

#define DUMP( x ) cerr << #x << " = " << ( x ) << endl

//     Λ   Λ＿_
//  ／(*ﾟーﾟ)／＼
// ／| ￣U U￣|＼／
//   |      |／

#include <random>
mt19937 rng;

class DisjointSetForest
{
private:
	const int N;

	vector<int> parent;
	vector<int> rank;

	int groups_;
	std::vector< int > sizes;

public:
	DisjointSetForest( int n ) : N( n ), parent( N ), rank( N, 0 ), groups_( N ), sizes( N, 1 )
	{
		std::iota( parent.begin(), parent.end(), 0 );

		return;
	}

	int find( int x )
	{
		if ( parent[x] == x )
		{
			return x;
		}
		return parent[x] = find( parent[x] );
	}

	bool same( int x, int y )
	{
		return find( x ) == find( y );
	}

	bool unite( int x, int y )
	{
		x = find( x );
		y = find( y );

		if ( x == y )
		{
			return false;
		}

		if ( rank[x] < rank[y] )
		{
			parent[x] = y;
			sizes[y] += sizes[x];
		}
		else
		{
			parent[y] = x;
			sizes[x] += sizes[y];

			if ( rank[x] == rank[y] )
			{
				++rank[x];
			}
		}

		--groups_;
		return true;
	}

	int groups() const
	{
		return groups_;
	}

	int groupSize( const int x )
	{
		return sizes[ find( x ) ];
	}
};
// DisjointSetForest( N )
// find( x )
// same( x, y )
// unite( x, y )
// groups()
// groupSize( x )

namespace Global
{
	int N, C, D, S;
	VT< VVI > Perms;
	VVI X, Y, T;
}

constexpr int dy[] = { 0, 0, 1, 0, -1 };
constexpr int dx[] = { 0, 1, 0, -1, 0 };
const string DIR = "-RDLU";

bool inside( const int y, const int x )
{
	return 0 <= y && y < Global::N && 0 <= x && x < Global::N;
}

int distance( const int y1, const int x1, const int y2, const int x2 )
{
	return abs( y1 - y2 ) + abs( x1 - x2 );
}

int score( const VS &moves )
{
	VI ys( Global::D ), xs( Global::D );
	REP( i, Global::D )
	{
		ys[i] = Global::Y[i][0];
		xs[i] = Global::X[i][0];
	}

	VVI cs = VVI( Global::N, VI( Global::N ) );

// 	DUMP( Global::Y[0] );
// 	DUMP( Global::X[0] );
// 	DUMP( Global::T[0] ) << endl;
// 	DUMP( Global::Y[1] );
// 	DUMP( Global::X[1] );
// 	DUMP( Global::T[1] );
// 	FOR( row, moves )
// 	{
// 		DUMP( row );
// 	}
// 	cerr << endl;


	int res = 0;
	REP( t, Global::S )
	{
		REP( i, Global::D )
		{
			if ( SZ( moves[t] ) <= i )
			{
				continue;
			}

			const int cy = ys[i];
			const int cx = xs[i];

			const int dir = find( ALL( DIR ), moves[t][i] ) - begin( DIR );
			const int ny = cy + dy[ dir ];
			const int nx = cx + dx[ dir ];

			const int tt = upper_bound( ALL( Global::T[i] ), t ) - begin( Global::T[i] );
			const int ty = Global::Y[i][ tt ];
			const int tx = Global::X[i][ tt ];

			if ( !inside( ny, nx ) || Global::T[i][ tt ] - t - 1 < distance( ny, nx, ty, tx ) )
			{
				cerr << t << ' ' << i << endl;
				DUMP( Global::T[i][ tt ] );
				DUMP( t );
				DUMP( i );
				DUMP( moves[t][i] );
				DUMP( ny );
				DUMP( nx );
				DUMP( ty );
				DUMP( tx );
				DUMP( distance( ny, nx, ty, tx ) );
				DUMP( Global::T[i][ tt ] - t - 1 );
				assert( false );
				const int d = distance( ny, nx, ty, tx );
				res += d * d * d;
			}

			if ( inside( ny, nx ) && dir )
			{
				++cs[ ny ][ nx ] %= Global::C;
			}

			ys[i] = ny;
			xs[i] = nx;
		}
	}

	{
		DisjointSetForest dsf( Global::N * Global::N );
		const auto grid_id = [&]( const int y, const int x )
		{
			return y * Global::N + x;
		};

		REP( i, Global::N )
		{
			REP( j, Global::N )
			{
				if ( i + 1 < Global::N && Global::Perms[i][j][ cs[i][j] ] == Global::Perms[ i + 1 ][j][ cs[ i + 1 ][j] ] )
				{
					dsf.unite( grid_id( i, j ), grid_id( i + 1, j ) );
				}
				if ( j + 1 < Global::N && Global::Perms[i][j][ cs[i][j] ] == Global::Perms[i][ j + 1 ][ cs[i][ j + 1 ] ] )
				{
					dsf.unite( grid_id( i, j ), grid_id( i, j + 1 ) );
				}
			}
		}
		
		VT< set< int > > groups( Global::C );
		REP( i, Global::N )
		{
			REP( j, Global::N )
			{
				groups[ Global::Perms[i][j][ cs[i][j] ] ].insert( dsf.find( grid_id( i, j ) ) );
			}
		}

		REP( i, Global::C )
		{
			const int g = SZ( groups[i] );
			res += g * g;
		}
	}

	return res;
}

VS pack( const VT< VS > &paths )
{
	VS res( Global::S, string( Global::D, '-' ) );

	REP( i, Global::D )
	{
		const string s = accumulate( ALL( paths[i] ), string() );
		REP( j, Global::S )
		{
			res[j][i] = s[j];
		}
	}

	return res;
}

VS solve()
{
	VT< VS > paths( Global::D );
	REP( i, Global::D )
	{
		REP( j, SZ( Global::X[i] ) - 1 )
		{
			const int dy = Global::Y[i][ j + 1 ] - Global::Y[i][j];
			const int dx = Global::X[i][ j + 1 ] - Global::X[i][j];
			const int dt = Global::T[i][ j + 1 ] - Global::T[i][j];

			string p;
			if ( dy )
			{
				p += string( abs( dy ), 0 < dy ? 'D' : 'U' );
			}
			if ( dx )
			{
				p += string( abs( dx ), 0 < dx ? 'R' :  'L' );
			}
			p += string( dt - ( abs( dy ) + abs( dx ) ), '-' );

			random_shuffle( ALL( p ) );
			paths[i].PB( p );
		}
	}

	int current_score = score( pack( paths ) );

	const clock_t clock_start = clock();
	uniform_int_distribution< int > rng_D( 0, Global::D - 1 );

	constexpr double TIME_LIMIT = 9.0;
	while ( 1. * ( clock() - clock_start ) / CLOCKS_PER_SEC < TIME_LIMIT )
	{
		const int i = rng_D( rng );
		uniform_int_distribution< int > rng_P( 0, SZ( paths[i] ) - 1 );
		const int j = rng_P( rng );

		const string s = paths[i][j];
		random_shuffle( ALL( paths[i][j] ) );

		const int next_score = score( pack( paths ) );
		if ( !chmin( current_score, next_score ) )
		{
			paths[i][j] = s;
		}
	}

	const auto res = pack( paths );

	FOR( row, res )
	{
		DUMP( row );
	}
	return res;
}

int main()
{
	cin.tie( 0 );
	ios::sync_with_stdio( false );
	cout << setprecision( 12 ) << fixed;

	const clock_t clock_start = clock();

	cin >> Global::N >> Global::C >> Global::D >> Global::S;
	Global::Perms.resize( Global::N, VVI( Global::N, VI( Global::C ) ) );
	REP( i, Global::N )
	{
		REP( j, Global::N )
		{
			REP( k, Global::C )
			{
				IN( char, c );
				Global::Perms[i][j][k] = c - '0';
			}
		}
	}
	Global::X.resize( Global::D );
	Global::Y.resize( Global::D );
	Global::T.resize( Global::D );
	REP( i, Global::D )
	{
		IN( int, P );
		Global::X[i].resize( P );
		Global::Y[i].resize( P );
		Global::T[i].resize( P );
		REP( j, P )
		{
			cin >> Global::X[i][j] >> Global::Y[i][j] >> Global::T[i][j];
		}
	}

	const VS result = solve();
	cout << Global::S << endl;
	copy( ALL( result ), OSI< string >( cout, "\n" ) );
	cout << flush;

	clock_t clock_end = clock();
	cerr << "Time : " << 1. * ( clock_end - clock_start ) / CLOCKS_PER_SEC << endl;

	return 0;
}
