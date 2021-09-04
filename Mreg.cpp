// Include guard:
#ifndef FB_R_TREE
#define FB_R_TREE

#include <array>
#include <string>
#include <memory>
#include <unordered_map>
#include <unordered_set>
#include <list>
#include <stack>
#include <ctype.h>
#include <stdexcept>
#include <algorithm>
#include <vector>
#include <utility>
#include <iterator>
#include <cmath>
#include <chrono>
#include <stdint.h>
#include <iostream>
#include <list>
#include <queue>
#include <fstream>
#include <sys/resource.h>
#include <cstring>
//#include "cllist.cpp"
#include <regex>
#include "full_regex.cpp"
#include <optional>
#include <limits>

using regex=Fregex;

#ifndef FRB_VERBOSE
	#define FRB_VERBOSE false
#endif
#ifndef FRB_VERBOSE_ANALYSIS
	#define FRB_VERBOSE_ANALYSIS (FRB_VERBOSE && false)
#endif
#ifndef FRB_CLEAN
	#define FRB_CLEAN false
#endif
#ifndef FRB_PROFILE
	#define FRB_PROFILE false
#endif

#ifndef FRB_GENERATE
	#define FRB_GENERATE false
#endif
#ifndef FRB_STORE
	#define FRB_STORE true
#endif
#ifndef FRB_MATCH
	#define FRB_MATCH true
#endif
// Only match and do not process groups
#ifndef PLAIN_FRB_MATCH
	#define PLAIN_FRB_MATCH false
#endif


// First char is not 7, but this way
// we can save on some cycles,
// since we don't have to "remap"
// chars. First char is actually 32
// Defined both, so the first_char
// is for cache optimizations
#define first_char 32u
#define start_match_char  7u
#define last_char 127u
#define control_positions 7u
#define reserved_data_size 2^15

#define char_offset (control_positions - start_match_char)

#define node_length (last_char - start_match_char + control_positions)



// The order is thought to improve on cache.
// Only useful flags during compilation-time
// must be placed at the end, so that cache
// starts there and more used nodes are
// in the cache.

// The id of the added match string, to not 
// mistake groups that are from previous compilations
#define GROUP_ID 0u
// A pointer to a vector<uint> of nodes, from which 
// we were meant to merge, when we advance one char
#define GROUP 1u
// The next node we must route to
#define NEXT 2u
// The amount of nodes pointing to this node
#define LINKS 3u
// The final id of the match. 0 if the node is not final
#define FINAL 4u
// A pointer to a list of captures to keep track what
// sub-strings to get and what not
// Also contains a flag, which will return 
// to the start of the tree
// when detected, and when it ends, returns
// to the node 
#define WARP_CAPTURES 5u
#define WARP_MASK (std::numeric_limits<T>::max()>>1)

// Nodes in data [0 : node_length] used to aid
// in performance with pre-calculated statistics
//
// The number of added_id in the tree
#define NUM_ADDED 1
// The maximum length of a regex expression
#define MAX_REG_LENGTH 2
// The total length of the vector being used
#define SIZE 3

// The number to look for when looking for
// capture nodes
#define CAPTURE_NODE -1u

#define group_t std::unordered_set
#define capture_t std::list
#define branch_t std::unordered_set

// Regex to string translation
#define reg_d std::string("0123456789")
#define reg_w (reg_d+std::string("ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz"))
#define reg_n '\n'
#define reg_t '\t'
#define reg_r '\r'
#define reg_z '\0'
#define reg_s std::string({' ',reg_n,reg_t})
#define reg_dot (reg_w+reg_s+std::string("!@#$%^&*()_+{}[]'\\|\"/-=>?<ºª`~"))

#define ANALIZE_SEPARATE (first_char-1)
// Analizing the regex,
// the char* meaning of every regex
// instruction. Must be up to 32 max.
#define an_not_sq_brack 1
#define an_sq_brack 2
#define an_bb_brack_m_n 3
#define an_bb_brack__n 4
#define an_bb_brack_m_ 5
#define an_bb_brack_m 6
#define an_asterisk_question 7
#define an_plus_question 8
#define an_asterisk 9
#define an_plus 10
#define an_question 11
#define an_backw_slash 12
#define an_dot 13
#define an_start_paren 14
#define an_end_paren 15
#define an_or 16
#define an_warp 17


constexpr inline bool fnull(uint p){ return p != 0; }
inline bool is_regex(const char* expr){
	return *(expr-1) == '\\' && !(*(expr-1) == '\\' && ! isalpha(*expr));
}


template <typename T>
class Mreg{
	// Not all should be public, but I have yet to look up
	// how to make some variables only accessable from child
	public:
		// Take note of which pointers have been deleted
		std::unordered_set<T> deleted;
		std::list<capture_t<long unsigned int>*> unknown_ptrs;
		
		std::vector<bool> contains_captures;
		std::vector<T> nodes_captures;
		std::vector<const char*> str_captures;
		std::vector<const char*> str_starts;
		std::stack<T> warps;
		std::stack<const char*> str_warps;

		std::unordered_set<T> nodes_data_captures;

		std::queue<uint8_t> capture = std::queue<uint8_t>();
		// Also, I could turn WARP_CAPTURES to int and add the ids only.
		// capture end would be in last capture node + 1
	
		T max_str_size = 0;

		// 1111111 >> 1 = 01111111
		// ~0111111 = 10000000 (only select last bit)
		static constexpr T warp_mask = ~WARP_MASK;
		// 0111111 (select all but last bit)
		static constexpr T captures_mask = WARP_MASK;

		T added_id=1;

		// This will take the form of void* in positions 0..control_positions
		// and of int in control_positions+1..node_length
		std::vector<T> data;
  
  
	Mreg() {
		this->data = std::vector<T>(node_length*2, 0);
		this->data.reserve(reserved_data_size);

		this->contains_captures = std::vector<bool> ();
		this->nodes_captures = std::vector<T>();
		this->str_captures = std::vector<const char*>();
		this->str_starts = std::vector<const char*>();
		this->warps = std::stack<T>();
		this->str_warps = std::stack<const char*>();

		this->nodes_data_captures = std::unordered_set<T>();


		this->contains_captures.push_back(false);
	}

	~Mreg(){
		this->delete_pointers();

		// TODO: Find where any of these are deleted 
		if(false && this->str_captures.size()){
			for(const char* scap: this->str_captures)
				delete[] scap;
		}
		if(this->str_starts.size()){
			printf("str_starts\n"); fflush(stdout);
			for(const char* ssta: this->str_starts)
				delete[] ssta;
		}
	}

	void delete_pointers(bool all = false){
		#if !FRB_GENERATE
		this->deleted = std::unordered_set<T> {};
		#endif

		const size_t max_size = this->data.size();
	
		#if FRB_VERBOSE
		printf("\n\n### DELETING\n\t");
		
		constexpr uint max = 5;
		uint count = 0;
		#endif

		for(uint node = node_length; node != max_size; node += node_length){
			if(this->nodes_data_captures.count(node))
				continue;

			#if FRB_VERBOSE
			printf(" %u", node);
			#endif

			if(this->data[node+GROUP] && static_cast<size_t>(this->data[node+GROUP]) > this->data.size()){
				#if FRB_VERBOSE
				printf("-G", this->data[node+GROUP]);
				#endif
				if(! deleted.count(this->data[node+GROUP])){
					#if FRB_VERBOSE
					printf("#");
					
					#endif

					deleted.insert(this->data[node+GROUP]);

					delete reinterpret_cast<group_t<uint>*>(this->data[node+GROUP]);
				}
				this->data[node+GROUP] = 0;
			}
			
			#if !PLAIN_FRB_MATCH
			if(all)
			#endif
			if(this->data[node+WARP_CAPTURES]){
				#if FRB_VERBOSE
				printf("-C");
				#endif
				if(! deleted.count(this->data[node+WARP_CAPTURES])){
					#if FRB_VERBOSE
					printf("#");
					#endif
					deleted.insert(this->data[node+WARP_CAPTURES]);

					delete reinterpret_cast<capture_t<long unsigned int>*>(this->data[node+WARP_CAPTURES]);
				}
				// Used in match to detect nodes with possible
				// captures
				#if PLAIN_FRB_MATCH
				this->data[node+WARP_CAPTURES] = 0;
				#endif
			}

			#if FRB_VERBOSE
			if(count != max)
				++count;
			else{
				count = 0;
				printf("\r%c[2K\r\t", 27);
			}
			#endif
		}

		// For all pointers in this->unknown_ptrs, check if they are
		// in deleted. If they are not in deleted,
		// delete the pointer.
		for(std::list<capture_t<long unsigned int>*>::iterator it = this->unknown_ptrs.begin(); it != this->unknown_ptrs.end(); ++it){
			T ptr = reinterpret_cast<T>(*it);
			if(deleted.count(ptr))
				continue;
			
			delete *it;

			deleted.insert(ptr);
		}
		this->unknown_ptrs.clear();

		#if FRB_VERBOSE
		printf("\n###\n\n");
		#endif
	}

	std::string str(const uint node=node_length){
		std::string result = "[";

		#if FRB_VERBOSE
		printf("Seen ");
		bool seen = false;
		#endif
		for(uint lett = control_positions; lett < node_length; ++lett){
			if(this->data[node+lett]){
				#if FRB_VERBOSE
				printf("%c ", lett-char_offset);
				seen = true;
				#endif
				result.append(std::string({static_cast<char>(lett-char_offset), ',', ' '}));
			}
		}
		#if FRB_VERBOSE
		if(! seen)
			printf("nothing ");

		printf("in str()\n");
		#endif

		result = result.substr(0, result.length()-2);
		result.append(std::string("]"));
		return result;
	}
	
	const char* c_str(const uint node=node_length){
		return this->str(node).c_str();
	}

	// Generates a new node at the end of data and 
	// returns it.
	inline T new_node(){
		T new_node = this->data.size();
		this->data.insert(this->data.end(), node_length, 0);

		#if FRB_VERBOSE
		printf("   Generated new node: %u\n", new_node);
		#endif

		return new_node;
	}

	void clean(){
		// Breath, hash and remove 
		printf("\n\n### CLEANING\n");

		this->_clear_capture_vectors();
		this->_move_captures();

	}
	
	void _clear_capture_vectors(){
		std::unordered_map<T, uint> capture_data_start = std::unordered_map<T, uint>();
		std::unordered_map<uint, uint> capture_data_space = std::unordered_map<uint, uint>();
		const size_t max_size = this->data.size();
	
		uint capture_cell;

		for(uint node = node_length; node != max_size; node += node_length){
			// If the node is a reallocated capture node, no need 
			// to iterate over it
			if(this->data[node] == CAPTURE_NODE)
				continue;

			// If the node has a capture vector
			// and it is a pointer (gt data.size())
			if(this->data[node+WARP_CAPTURES]){
				if(this->data[node+WARP_CAPTURES] > static_cast<uint>(this->data.size())){
					// If we have not deleted this ptr yet
					if(! deleted.count(this->data[node+WARP_CAPTURES])){
						capture_t<long unsigned int>* captures = reinterpret_cast<capture_t<long unsigned int>*>(this->data[node+WARP_CAPTURES]);
						
						captures->sort();
						captures->reverse();

						deleted.insert(this->data[node+WARP_CAPTURES]);

						std::unordered_map<uint, uint>::iterator spaces_iter = capture_data_space.begin();

						for(; spaces_iter != capture_data_space.end(); ++spaces_iter){
							// Space_left + captures.size + 1 <= node_length
							if(spaces_iter->second+captures->size() < node_length)
								break;
						} 


						#if FRB_VERBOSE
						printf("\tNew ptr 0x%X in node %u\n\t", this->data[node+WARP_CAPTURES], node);
						#endif

						if(spaces_iter == capture_data_space.end()){
							capture_cell = this->new_node();
							this->nodes_data_captures.insert(capture_cell);

							// Take note of the size of the vector
							// we are writing down.
							capture_data_space[capture_cell] = captures->size()+2;

							// Mark as a node that holds only captures
							// Start in cell 1 (zero ocupied)
							this->data[capture_cell] = CAPTURE_NODE;
							++capture_cell;
						} else {
							capture_cell = spaces_iter->first + spaces_iter->second;
							spaces_iter->second += captures->size()+1;
						}

						#if FRB_VERBOSE
						printf("\t Contains %zu capture nodes\n\t  [", capture_cell, captures->size());
						#endif
						
						capture_data_start[this->data[node+WARP_CAPTURES]] = capture_cell;
						this->data[capture_cell] = captures->size();

						// Take note the new direction assigned
						this->data[node+WARP_CAPTURES] = capture_cell;

						for(long int captured_node : *captures){
							++capture_cell;
							this->data[capture_cell] = captured_node;
							#if FRB_VERBOSE
							printf("  %d[%u]", captured_node, capture_cell);
							#endif
						}

						#if FRB_VERBOSE
						printf(" ]\n");
						#endif

						delete captures;
					}
					// If we deleted it, access to the capture cell in the umap
					else {
						//printf("TEST\n"); fflush(stdout);

						typename
						std::unordered_map<T, uint>::const_iterator seen_cell = 
								capture_data_start.find(this->data[node+WARP_CAPTURES]);

						if(seen_cell != capture_data_start.cend()){
							this->data[node+WARP_CAPTURES] = seen_cell->second;

							#if FRB_VERBOSE
							printf("\tSeen ptr 0x%X in node %u\n\t Redirected to %u\n", 
										this->data[node+WARP_CAPTURES], node, seen_cell->second);
							#endif
						} else {
							printf("[!]\n[!] ERROR: Missing ptr in %u (0x%x)\n[!]\n\n\n", node, this->data[node+WARP_CAPTURES]);
							this->data[node+WARP_CAPTURES] = 0;
						}
					}
				}
			}
		}
		#if FRB_VERBOSE
		printf("### Size %zu -> %zu\n\n", max_size, this->data.size());
		fflush(stdout);
		#endif
	}

	void _move_captures(){
		T first_valid = this->data.size();
		const T first_invalid = this->warp_mask - node_length;

		#if FRB_VERBOSE
		printf("first invalid node : %d\n", first_invalid);
		#endif

		while(first_valid >= first_invalid)
			first_valid -= node_length;

		#if FRB_VERBOSE
		printf("first valid node : %zu\n\n", first_valid);
		#endif

		std::vector<T> cap_to_move {};

		// Copy invalid captures nodes to cap_to_move,
		// and lower the first valid, since there
		// needs to fit the invalid nodes in a valid zone
		for(T node : this->nodes_captures)
			if(node >= first_invalid){
				#if FRB_VERBOSE
				printf("  [-] Detected invalid node %zu\n", node);
				#endif
				cap_to_move.push_back(node);

				first_valid -= node_length;
			}

		// First valid is unchanged because every time we
		// move a node, the previous is pushed forward
		// (can't be pushed backwards, since)
		// these nodes will always be in an invalid
		// position, which is greater than the first valid
		for(T node : cap_to_move)
			this->move_node(node, first_valid);
	}

	// This function moves a given node to a position,
	// displacing all other nodes from behind one position.
	// This is useful to optimize cache loading
	// and it is necessary to join the warp bit to
	// the captures position, since T has a specific
	// length (in bits) to optimize it, to being
	// able to optimize it, I need to check no 
	// captures node number uses all bits, so that
	// the last one can become the warp flag.
	// Since captures and warp is checked every
	// char in match(), not accessing the array
	// again should free some clock cycles.
	void move_node(T node_from, T node_to){
		#if FRB_VERBOSE
		printf("Moving node %d -> %d\n", node_from, node_to);
		#endif
		T* aux = new T[node_length];

		__builtin_prefetch(&this->data[node_from]);

		// copy node_from to aux
		T positions = node_length+1;
		while(--positions)
			*(aux + positions) = this->data[node_from+positions];
		*aux = this->data[node_from];

		// copy (node_from + n <- node_from + n+1)
		if(node_from < node_to){
			// Since we start moving data to node_from, 
			// to_iter points to node_from.
			T* to_iter = this->data.data() + node_from;
			T* from_iter = to_iter + node_length;
			T* goal = this->data.data() + node_to + node_length;

			while(from_iter != goal)
				*(to_iter++) = *(from_iter++);

		// node_from > node_to
		// copy (node_from - n-1 -> node_from - n)
		} else {
			T* from_iter = this->data.data() + node_from - 1;
			// Since we start moving data to node_from, 
			// to_iter points to node_from.
			T* to_iter = from_iter + node_length;
			
			T* goal = this->data.data() + node_to;

			while(from_iter != goal)
				*(to_iter--) = *(from_iter--);
		}

		// Copy back node_from (in aux) to node_to
		positions = node_length+1;
		while(--positions)
			this->data[node_to+positions] = *(aux + positions);
		this->data[node_to] = *aux;

		delete[] aux;
	}

	inline std::ostream& store(std::ostream& out_stream){
		#if FRB_VERBOSE
		printf("Serializing all %zu data pos... \n", this->data.size());
		#endif
		
		const size_t data_size = this->data.size();

		out_stream.write(reinterpret_cast<char const*>(&data_size), sizeof(data_size));
		out_stream.write(reinterpret_cast<char const*>(this->data.data()), data_size*sizeof(T));

		#if !FRB_CLEAN || FRB_VERBOSE
		printf("[#] Data serialized.\n\n");
		#endif

		return out_stream;
	}

	inline std::istream& load(std::istream& in_stream){
		#if FRB_VERBOSE
		printf("Loading all ");
		#endif
		decltype(this->data.size()) size;
		in_stream.read(reinterpret_cast<char *>(&size), sizeof(size));
		
		#if FRB_VERBOSE
		printf("%zu data pos... ", size);
		#endif

		this->data.resize(size);
		in_stream.read(reinterpret_cast<char *>(this->data.data()), this->data.size() * sizeof(T));

		#if !FRB_CLEAN || FRB_VERBOSE
		printf("[#] Data deserialized.\n\n");
		#endif

		this->nodes_captures.reserve(this->data[MAX_REG_LENGTH]);
		this->str_captures.reserve(this->data[MAX_REG_LENGTH]);
		this->str_starts.reserve(this->data[MAX_REG_LENGTH]);
		this->added_id = this->data[NUM_ADDED];

		this->restore_captures();

		return in_stream;
	}

	static inline T load_position(std::istream& in_stream, uint pos){
		#if FRB_VERBOSE
		printf("Loading position %i of data\n", pos);
		#endif

		std::vector<T> positions = std::vector<T>();

		in_stream.read(reinterpret_cast<char *>(positions.data()), pos * sizeof(uintptr_t));

		return positions.back();
	}

	void restore_captures(){
		this->contains_captures.insert(
				this->contains_captures.cend(), this->added_id+1, false);
		const size_t max_size = this->data.size();

		#if FRB_VERBOSE
		printf("Restoring captures:\n");

		std::unordered_set<uint> seen = std::unordered_set<uint>();
		#endif

		int captured_id;

		for(uint node = node_length; node != max_size; node += node_length){
			if(this->data[node] == CAPTURE_NODE){
				#if FRB_VERBOSE
				printf("Node %u is a capture node\n", node);
				#endif

				++node;
				while(this->data[node] != 0){
					//printf("node %u of length: %u\n", node, this->data[node]);
					for(uint captured = this->data[node++]; captured != 0; --captured, ++node){
						//printf("%u %u %u\n", node, this->data[node], captured);
						captured_id = abs(static_cast<int>(this->data[node]));
						this->contains_captures[captured_id] = true;

						#if FRB_VERBOSE
						if(! seen.count(captured_id)){
							printf("Detected captures in id: %u\n", captured_id);

							seen.insert(captured_id);
						}
						#endif
					}
				}

				#if FRB_VERBOSE
				printf("Return to initial node cell from %u -> ", node);
				#endif
				// Return to node % node_length = 0
				node -= node % node_length;
				#if FRB_VERBOSE
				printf("%u\n", node);
				#endif
			}
		}

		#if FRB_VERBOSE
		printf("\n");
		#endif
		#if !FRB_CLEAN || FRB_VERBOSE
		printf("Ids with captures are:\n ");
		
		for(uint capture_id = 1; capture_id != this->contains_captures.size(); ++capture_id)
			if(this->contains_captures[capture_id])
				printf("%u ", capture_id);

		printf("\n\n");
		#endif

		this->data[SIZE] = this->data.size(); 
	}

	inline T count_sorted(T node, const T value)
		__attribute__ ((const))
		#if !FRB_PROFILE
		__attribute__ ((always_inline))
		#endif
		__attribute__ ((hot))
	{
		#if FRB_VERBOSE
		printf("CS[%u,%d|%u]:", node, this->data[node], value);
		#endif
		const T end = node + this->data[node] + 1;

		++node;
		if(this->data[node] > value){
			#if FRB_VERBOSE
			printf(" - None\n");
			#endif
			return 0;
		}
		++node;

		T result = 0;
		while(this->data[node] < value){
			if(node == end){
				#if FRB_VERBOSE
				printf(" - None\n");
				#endif

				return 0;
			}

			#if FRB_VERBOSE
			printf(" %u", this->data[node]);
			#endif
			++node;
		}

		while(node != end && this->data[node] == value){
			++result;
			#if FRB_VERBOSE
			printf(" N%u", node);
			#endif
			++node;
		}
			
		#if FRB_VERBOSE
		printf("\n", node);
		#endif
		return result;
	}

	inline T count_sorted_backw(T node, const T value)
		__attribute__ ((const))
		#if !FRB_PROFILE
		__attribute__ ((always_inline))
		#endif
		__attribute__ ((hot))
	{
		#if FRB_VERBOSE
		printf("CSB[%u,%d|%u]:", node, this->data[node], value);
		#endif
		const T end = node;
		const T max = this->added_id + 1;
		node += this->data[node];

		#if FRB_VERBOSE
		printf(" %u", this->data[node]);
		
		#endif

		if(this->data[node] < value || this->data[node] > max){
			#if FRB_VERBOSE
			printf(" - None\n");
			#endif
			return 0;
		}

		T result = 0;
		while(this->data[node] < max && this->data[node] > value){
			if(node == end){
				#if FRB_VERBOSE
				printf(" - None\n");
				#endif

				return 0;
			}

			#if FRB_VERBOSE
			printf(" %u", this->data[node]);
			#endif
			--node;
		}

		while(node != end && this->data[node] == value){
			++result;
			#if FRB_VERBOSE
			printf(" N%u", node);
			#endif
			--node;
		}

		#if FRB_VERBOSE
		printf("\n");
		#endif

		return result;
	}

	T match(const char * str)
		# if !FRB_PROFILE
		//__attribute__ ((always_inline))
		//__attribute__ ((flatten))
		#endif
		//__attribute__ ((hot))
		// Should it have a const attribute?
		
	{
		// In the future, it could be added a find() 
		// to improve efficiency in the not-so-rare case of
		// any of . and + or * followed by a unique char
		// Pex "\(.*?\)" instead of just iterating over the string,
		// find the next character, without any vector access.
		// Is it worth it? Not hard to implement, but it would mean
		// Another access per char.
		// Maybe since capture start & end happens not so often, 
		// I could add a control position of (capture or find)
		// and in case of being true, check both. It could allow me
		// to add improvements about corner cases, without affecting
		// performance too much. I think i will do so
		// Is there a way to check for \d & \w too? 
		// Something like hash matching?

		// To capture data, add an array of vector and keep adding 
		// points of start & finish of any possible match, when
		// node+start_capture and node+end_capture. 
		T mreg = node_length;

		this->nodes_captures.clear();
		this->str_captures.clear();

		#if FRB_VERBOSE
		printf("match start %c, 0x%x\n", *str, this->data[mreg+*str+char_offset]);

		T last_id = mreg;

		std::list<char> restart_str = std::list<char>();
		#endif

		// Profiler: this is match()

		// Not necessary, but tell the compiler that data
		// is important and must be cached from that address
		__builtin_prefetch(&this->data[node_length+WARP_CAPTURES]);

		#if !PLAIN_FRB_MATCH
		// If contains any captures in the initial node
		if(this->data[mreg+WARP_CAPTURES]){
			#if FRB_VERBOSE
			printf("Detected captures in node %u [%X]\n", mreg, this->data[mreg+WARP_CAPTURES]);
			
			restart_str.push_back(*str);
			#endif	
			this->nodes_captures.push_back(this->data[mreg+WARP_CAPTURES]);
			this->str_captures.push_back(str);
		}
		#endif

		while(*str && (mreg = this->data[mreg+*str+char_offset])){
			#if FRB_VERBOSE
			printf("match %c (%i)\n", *str, *str);
			
			printf("%u -> %u\n", last_id, mreg);
			last_id = mreg;
			#endif
			
			#if !PLAIN_FRB_MATCH
			if(this->data[mreg+WARP_CAPTURES]){
				#if FRB_VERBOSE
				printf("Detected captures in node %u [%u]\n", mreg, this->data[mreg+WARP_CAPTURES]);
			
				restart_str.push_back(*str);
				#endif
				this->nodes_captures.push_back(this->data[mreg+WARP_CAPTURES]);
				this->str_captures.push_back(str);
			}
			#endif

			++str;
		}

		const T final = this->data[mreg+FINAL];

		#if FRB_VERBOSE
			printf("mat2 - id: %u\nEnd: %s\n", final, this->c_str(mreg));

		#endif

		if((!*str) && final){ [[likely]];
			#if !PLAIN_FRB_MATCH
			if(! this->contains_captures[final]){
				#if FRB_VERBOSE
				printf("Id %u does NOT contain captures.\n", final);
				#endif

				return final;
			}

			typename
			std::vector<T>::const_iterator nodes_iter = this->nodes_captures.cbegin();
			
			typename
			std::vector<T>::const_iterator nodes_end = this->nodes_captures.cend();
			
			std::vector<const char*>::const_iterator str_iter = this->str_captures.cbegin();
			
			#if FRB_VERBOSE
			std::list<char>::const_iterator print_iter = restart_str.cbegin();
			#endif

			{

			T starting_captures = 0;
			// The first node with should only have starting captures, 
			// find the first containing final
			for(; nodes_iter != nodes_end && !starting_captures; ++nodes_iter, ++str_iter){
				// Search in reverse because starting groups are positive
				starting_captures = this->count_sorted_backw(*nodes_iter, final);
				#if FRB_VERBOSE
				printf("SC: %u\n", starting_captures);
				
				++print_iter;
				#endif
			}

			// Should be removed. Either contains_captures is wrong, or
			// checking for starting captures is somehow wrong.
			if(! starting_captures){
				#if FRB_VERBOSE
				printf("[-]Contains captures was true, but we did not find any captures\n");
				#endif

				return -1;
			}
			#if FRB_VERBOSE
			printf(" Start capture in char: %c\n", *print_iter);
			++print_iter;
			#endif

			T starts = 0;
			for(; starting_captures; --starting_captures, ++starts)
				this->str_starts.push_back(*str_iter);
			
			std::string buffer = std::string();
			const char* group_start;
			char *subStr;

			T new_groups, char_dist;

			// We can do while because we have not returned,
			// so, at least once we have to search for starting/final nodes
			while(nodes_iter != nodes_end){
				for(new_groups = this->count_sorted(*nodes_iter, -final); 
							new_groups; --new_groups){
					group_start = this->str_starts.back();
					this->str_starts.pop_back();
					
					subStr = static_cast<char*>(
						calloc(std::distance(group_start, *str_iter), sizeof(char))); 
					memcpy(subStr, group_start, std::distance(group_start, *str_iter));

					#if FRB_VERBOSE
					printf(" End capture in char: %c\n", *print_iter);

					printf("----%s-\n", subStr);
					#endif
				}

				for(new_groups = this->count_sorted_backw(*nodes_iter, final); new_groups; --new_groups){
					this->str_starts.push_back(*str_iter);
					
					#if FRB_VERBOSE
					printf(" Start capture in char: %c\n", *print_iter);
					#endif
				}
				
				++str_iter;
				++nodes_iter;
				#if FRB_VERBOSE
				++print_iter;
				#endif
			}

			#if FRB_VERBOSE
			if(this->str_starts.size())
				printf("# End of the string\n");
			#endif

			for(const char* last_str : this->str_starts){
				subStr = static_cast<char*>(
						calloc(std::distance(last_str, str), sizeof(char))); 
				memcpy(subStr, last_str, std::distance(last_str, str));

				#if FRB_VERBOSE
				printf("----%s-\n", subStr);
				#endif
			}

			this->str_starts.clear();
	
			}
			#endif
			return final;
		}

		return 0;
	}

		uint match_and_subgroups(const char * str)
		# if !FRB_PROFILE
		__attribute__ ((always_inline))
		__attribute__ ((flatten))
		#endif
		__attribute__ ((hot))
		// Should it have a const attribute?
		
	{
		T mreg = node_length;

		this->nodes_captures.clear();
		this->str_captures.clear();

		#if FRB_VERBOSE
		printf("match start %c, 0x%x\n", *str, this->data[mreg+*str+char_offset]);

		uint last_id = mreg;

		std::list<char> restart_str = std::list<char>();
		#endif

		// Profiler: this is match()

		// Not necessary, but tell the compiler that data
		// is important and must be cached from that address
		//__builtin_prefetch(&this->data[node_length+WARP_CAPTURES]);

		#if !PLAIN_FRB_MATCH
		// If contains any captures in the initial node
		if(this->data[mreg+WARP_CAPTURES]){
			#if FRB_VERBOSE
			printf("Detected captures in node %u [%X]\n", mreg, this->data[mreg+WARP_CAPTURES]);
			
			restart_str.push_back(*str);
			#endif	
			this->nodes_captures.push_back(this->data[mreg+WARP_CAPTURES]);
			this->str_captures.push_back(str);
		}
		#endif

		do{
		while(mreg = this->data[mreg+*str+char_offset]){
			[[likely]];

// This is in case there
// is a warp
in_loop:
			#if FRB_VERBOSE
			printf("  match %c (%i)\n", *str, *str);
			
			printf("   %u -> %u\n", last_id, mreg);
			last_id = mreg;
			#endif
			
			#if !PLAIN_FRB_MATCH
			if(this->data[mreg+WARP_CAPTURES]){
				#if FRB_VERBOSE
				printf("[?] Detected captures in node %u [%u]\n", mreg, this->data[mreg+WARP_CAPTURES]);
			
				restart_str.push_back(*str);
				#endif
				this->nodes_captures.push_back(this->data[mreg+WARP_CAPTURES]);
				this->str_captures.push_back(str);
			}
			#endif

			#define WARP false
			
			#if WARP
			// Warps go back at the start of the tree to look for 
			// sub-groups.
			if(this->data[mreg+WARP_CAPTURES] & this->warp_mask){
				#if FRB_VERBOSE
				printf("[?] Detected warp node %u\n  Match continued in node %u\n", mreg, node_length);
				#endif

				this->warps.push(mreg);
				this->str_warps.push(str);

				mreg = node_length;
			}
			#endif

			if(!*++str)
				goto end_loop;
		}
		
		// No match, so return 0
		return 0;

		}while(1);
		// Here I need to check for warps. However,
		// since it is not yet implemented, just break

end_loop:

		const T final = this->data[mreg+FINAL];

		#if FRB_VERBOSE
			printf("mat2 - id: %u\nEnd: %s\n", final, this->c_str(mreg));

		#endif

		if((!*str) && final){ [[likely]];
			#if !PLAIN_FRB_MATCH
			if(! this->contains_captures[final]){
				#if FRB_VERBOSE
				printf("Id %u does NOT contain captures.\n", final);
				#endif

				return final;
			}

			typename
			std::vector<T>::const_iterator nodes_iter = this->nodes_captures.cbegin();

			typename
			std::vector<T>::const_iterator nodes_end = this->nodes_captures.cend();
			
			std::vector<const char*>::const_iterator str_iter = this->str_captures.cbegin();
			
			#if FRB_VERBOSE
			std::list<char>::const_iterator print_iter = restart_str.cbegin();
			#endif

			{

			T starting_captures = 0;
			// The first node with should only have starting captures, 
			// find the first containing final
			for(; nodes_iter != nodes_end && !starting_captures; ++nodes_iter, ++str_iter){
				// Search in reverse because starting groups are positive
				starting_captures = this->count_sorted_backw(*nodes_iter, final);
				#if FRB_VERBOSE
				printf("SC: %u\n", starting_captures);
				
				++print_iter;
				#endif
			}

			// Should be removed. Either contains_captures is wrong, or
			// checking for starting captures is somehow wrong.
			if(! starting_captures){
				#if FRB_VERBOSE
				printf("[-]Contains captures was false, but we did not find any captures\n");
				#endif

				return 0;
			}
			#if FRB_VERBOSE
			printf(" Start capture in char: %c\n", *print_iter);
			++print_iter;
			#endif

			T starts = 0;
			for(; starting_captures; --starting_captures, ++starts)
				this->str_starts.push_back(*str_iter);
			
			std::string buffer = std::string();
			const char* group_start;
			char *subStr;

			T new_groups, char_dist;

			// We can do while because we have not returned,
			// so, at least once we have to search for starting/final nodes
			while(nodes_iter != nodes_end){
				for(new_groups = this->count_sorted(*nodes_iter, -final); 
							new_groups; --new_groups){
					group_start = this->str_starts.back();
					this->str_starts.pop_back();
					
					subStr = static_cast<char*>(
						calloc(std::distance(group_start, *str_iter), sizeof(char))); 
					memcpy(subStr, group_start, std::distance(group_start, *str_iter));

					#if FRB_VERBOSE
					printf(" End capture in char: %c\n", *print_iter);

					printf("----%s-\n", subStr);
					#endif
				}

				for(new_groups = this->count_sorted_backw(*nodes_iter, final); new_groups; --new_groups){
					this->str_starts.push_back(*str_iter);
					
					#if FRB_VERBOSE
					printf(" Start capture in char: %c\n", *print_iter);
					#endif
				}
				
				++str_iter;
				++nodes_iter;
				#if FRB_VERBOSE
				++print_iter;
				#endif
			}

			#if FRB_VERBOSE
			if(this->str_starts.size())
				printf("# End of the string\n");
			#endif

			for(const char* last_str : this->str_starts){
				subStr = static_cast<char*>(
						calloc(std::distance(last_str, str), sizeof(char))); 
				memcpy(subStr, last_str, std::distance(last_str, str));

				#if FRB_VERBOSE
				printf("----%s-\n", subStr);
				#endif
			}

			this->str_starts.clear();
	
			}
			#endif
			return final;
		}

		return 0;
	}

	/* 
		Could be done a find/findall algorithm optimization,
		where we copy all prefixes from the tree to the subsequent
		nodes, with no performance nor spatial regression.
	*/
	
};

#if FRB_GENERATE
template <typename T>
int match(Mreg<T> &r)
#else
int main(int argc, char* argv[])
#endif
{
	#if FRB_MATCH
	// to be checked if they match (not all must match)
	std::vector<const char*> match {
						"hombros", "adios", "hombree", "ads",
						"hombro", "hombres", "hola ", "a1b",
						"hola", "hola.", "dios", "", "1",
						"Guapa", "guape", "guapi",
						"r@", "1@", "a@", "2@",
						".h.", ".@.", "haaaah",
						"haaah", "haaaaah", "loop",
						"looooooop", "lop", "limit",
						"limitt", "limittttt", "limitttttt",
						"1234", "aleluy", "aleluyaaa", "alelu",
						"numero", "numeros", "numer", "numeross",
						"chicosssss", "chicas", "chices", "chicus",
						"amigo!", "mi amigo!", "Hola, amigo!",
						"Hola, mi amigo!", "Hola,mi amigo!",
						"muy ", "muy buenas", "muybuenas",/*
						"buenas", "gracias", "muchas gracias",
						"muchas muchas muchas gracias",
						"pues", "pues si", "pues si si si",
						"tu sabes", "tu sabes sabes sabes", "tu",
						"no, mola", "no, no, no, mola", "mola",
						"muchas   gracias", "pues siii",
						"tu sabesssss", "no,    mola", 
						"muchasgracias", "no,mola"*/
						};

	// Ids start by 1 from the add array, since id=0 means no match
	std::vector<uint> id {
						2, 4, 0, 4, 3, 2,
						1, 11, 1, 7, 0, 
						0, 6, 8, 8, 0, 9, 
						9, 0, 0, 10, 10, 
						12, 0, 0, 13, 13,
						0, 0, 14, 14, 0,
						6, 15, 15, 0, 16,
						16, 0, 0, 17, 17,
						17, 0, 18, 18, 18,
						18, 0, 19, 19, 0, 
						0, 20, 20, 20, 21,
						21, 21, 22, 22, 0,
						22, 22, 0, 0, 0,
						0, 0, 0, 0
						};
	#endif

	#if FRB_VERBOSE
	std::unordered_set<uint> show {
		13
	};

	printf("#### Start ####\n");
	#endif

	typedef std::chrono::high_resolution_clock Clock;
	std::chrono::_V2::system_clock::time_point load_data_start, load_data_end,
											store_data_start, store_data_end;	

	#if !FRB_GENERATE
	std::fstream file;

	#define POSITION_SIZE 16

	#if POSITION_SIZE == 16
		Mreg<uint_fast16_t> r = Mreg<uint_fast16_t>();
	#elif POSITION_SIZE == 32
		Mreg<uint_fast32_t> r = Mreg<uint_fast32_t>();
	#elif POSITION_SIZE == 64
		Mreg<uint_fast64_t> r = Mreg<uint_fast64_t>();
	#else
		Mreg<uint_fast8_t> r = Mreg<uint_fast8_t>();
	#endif

    /*  Open the language JSON file as a fstream */
    file.open("FRB.tree", std::ios::in);
	
	load_data_start = Clock::now();
	r.load(file);
	load_data_end = Clock::now();

	file.close();
	#endif

	#if FRB_MATCH

	#if !FRB_VERBOSE
	printf("\n\nMatching:\n");

	// So that it appears in profiling:
	//for(const char* match_str : match){
	//	r.match(match_str);
	//}
	#endif

	std::vector<uint> match_ids {};
	match_ids.reserve(match.size());

	uint correct = 0, missed = 0, missmatched = 0;
	uint found;

	const uint match_size = static_cast<uint>(match.size());
	uint check = 0;

	#define matchf r.match

    auto match_regex_start = Clock::now();
	for(const char* match_str : match){
		#if FRB_VERBOSE
			found = matchf(match_str);

			if(show.size() && show.count(found))
				printf("\n\n###\n");

			if(found){
				printf("\t [%c] Match of \"%s\" [ match id = %u ]\n",
									(id[check]==found)?'+':'-',match_str,found);
				if(id[check]==found)
					++correct;
				else
					++missmatched;
			}
			else{
				printf("\t [%c] Not match of \"%s\"\n",
									(id[check]==0)?'+':'-', match_str);
				if(id[check]==0)
					++correct;
				else
					++missed;
			}

			if(show.size() && show.count(found))
				printf("\n###\n\n");

			++check;
		#else
			match_ids.push_back(matchf(match_str));
		#endif
	}
    auto match_regex_end = Clock::now();

	#if !FRB_CLEAN
	#if !FRB_VERBOSE
	printf("Matched %d strings:\n", match.size());

	for(check = 0; check < match.size(); ++check){
		found = match_ids[check];
		
		if(found){
			printf("\t [%c] Match of \"%s\" [ match id = %u ]\n",
								(id[check]==found)?'+':'-',match[check],found);
			if(id[check]==found)
				++correct;
			else
				++missmatched;
		}else{
			printf("\t [%c] Not match of \"%s\"\n",
								(id[check]==0)?'+':'-', match[check]);
			if(id[check]==0)
				++correct;
			else
				++missed;
		}
	}
	#endif
	#endif

	printf("\n#### RESULTS ####\n");

	#if FRB_MATCH
	printf(" (%d/%zu) of correct matches.\n", correct, match.size());
	if(missmatched)
		printf("    [%d of which, missmatched]\n", missmatched);
	if(missed)
		printf("    [%d of which, missed matches]\n", missed);
	printf("  %.1f%% of correct matches.\n\n", static_cast<float>(correct*100)/match.size());
	#endif

	printf("  Size of data: %ld | (SIZE_POS: %d)\n", r.data.size(),
				static_cast<int>(pow(2, ceil(log(ceil(log(r.data.size())/log(2)))/log(2)))));

	#if FRB_VERBOSE
	printf("\n[!] WARNING: Prints enabled. Expect performance regression.");
	#endif
	printf("\n#### TIMINGS ####\n");


	#if FRB_MATCH
	std::chrono::nanoseconds match_time = std::chrono::duration_cast<std::chrono::nanoseconds>(
										match_regex_end-match_regex_start);

	std::chrono::nanoseconds load_time = std::chrono::duration_cast<std::chrono::nanoseconds>(
										load_data_end-load_data_start);

	std::cout << " Data loading : " << load_time.count() <<" ns.\n";
	std::cout << " Matching ("<< match.size() <<" regex) : "<< match_time.count() <<" ns.\n";
	std::cout << " Matching     (Avg.) : "<< match_time.count()/match.size() <<" ns.\n";
	#endif

	printf("#################\n");
	#endif

	return 0;
}


#endif
