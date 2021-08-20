// Import guard:
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

using regex=Fregex;

#ifndef FRB_VERBOSE
	#define FRB_VERBOSE false
#endif
#ifndef FRB_CLEAN
	#define FRB_CLEAN false
#endif
#ifndef FRB_PROFILE
	#define FRB_PROFILE true
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


// The order is thought to improve on cache.
// Only useful flags during compilation-time
// must be placed at the end, so that cache
// starts there and more used nodes are
// in the cache.

// The id of the added match string, to not 
// mistake groups that are from previous compilations
#define GROUP_ID 0
// A pointer to a vector<uint> of nodes, from which 
// we were meant to merge, when we advance one char
#define GROUP 1
// The next node we must route to
#define NEXT 2
// The amount of nodes pointing to this node
#define LINKS 3
// The final id of the match. 0 if the node is not final
#define FINAL 4
// A pointer to a list of captures to keep track what
// sub-strings to get and what not
#define CAPTURES 5
// The next node after a sub-group.
// This will return to the start of the tree
// when detected, and when it ends, returns
// to the node pointed in this field.
// Ideally it should be merged with "FINAL".
// Not only they align in purpose, they will
// fit in the same node, because they are
// intended for pointers, but positions in
// the array are much shorter.
#define WARP 6

// Nodes in data [0 : char_length] used to aid
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

// First char is not 7, but this way
// we can save on some cycles,
// since we don't have to "remap"
// chars. First char is actually 32
#define first_char  7
#define last_char 127
#define control_positions 7
#define reserved_data_size 2^15

#define char_offset (control_positions - first_char)

#define char_length (last_char - first_char + control_positions)

// Regex to string translation
#define reg_d std::string("0123456789")
#define reg_w reg_d+std::string("ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz")
#define reg_n '\n'
#define reg_t '\t'
#define reg_r '\r'
#define reg_z '\0'
#define reg_s std::string({' ',reg_n,reg_t})
#define reg_dot reg_w+reg_s+std::string("!@#$%^&*()_+{}[]'\\|\"/-=>?<ºª`~")

#define ANALIZE_SEPARATE 31
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


constexpr inline bool fnull(uint p){ return p != 0; }
inline bool is_regex(const char* expr){
	return *(expr-1) == '\\' && !(*(expr-1) == '\\' && ! isalpha(*expr));
}


template <typename T>
class Mreg{
	private:
		// Take note of which pointers have been deleted
		std::unordered_set<T> deleted {};
		std::list<capture_t<long int>*> unknown_ptrs;
		
		std::vector<bool> contains_captures;
		std::vector<T> nodes_captures;
		std::vector<const char*> str_captures;
		std::vector<const char*> str_starts;

		std::unordered_set<T> nodes_data_captures;

		std::queue<uint8_t> capture = std::queue<uint8_t>();
		// Also, I could turn CAPTURES to int and add the ids only.
		// capture end would be in last capture node + 1
	
		uint max_str_size = 0;

		bool analizer_generated = false;
		std::vector<std::pair<regex, std::unordered_map<char, uint>>> regex_analizer;
	public:
		uint added_id=1;
		// In a future, they will be private
		//std::array<uint, char_length>* count = new std::array<uint, char_length>();
		//std::array<uint, char_length>* storage = new std::array<uint, char_length>();

		// This will take the form of void* in positions 0..control_positions
		// and of int in control_positions+1..char_length
		std::vector<T> data;
  
  
	Mreg() {
		this->data = std::vector<T>(char_length*2, 0);
		this->data.reserve(reserved_data_size);

		this->contains_captures = std::vector<bool> ();
		this->nodes_captures = std::vector<T>();
		this->str_captures = std::vector<const char*>();
		this->str_starts = std::vector<const char*>();
		this->unknown_ptrs = std::list<capture_t<long int>*>();

		nodes_data_captures = std::unordered_set<T>();


		this->contains_captures.push_back(false);
	}

	~Mreg(){
		//this->delete_pointers();
		this->data.resize(0);
	}

	void delete_pointers(bool all = false){
		const size_t max_size = this->data.size();
	
		#if FRB_VERBOSE
		printf("\n\n### DELETING\n\t");
		
		constexpr uint max = 5;
		uint count = 0;
		#endif

		for(uint node = char_length; node != max_size; node += char_length){
			if(this->nodes_data_captures.count(node))
				continue;

			#if FRB_VERBOSE
			printf(" %u", node);
			#endif

			if(this->data[node+GROUP]){
				#if FRB_VERBOSE
				printf("-G", this->data[node+GROUP]);
				#endif
				if(! this->deleted.count(this->data[node+GROUP])){
					#if FRB_VERBOSE
					printf("#");
					
					#endif

					this->deleted.insert(this->data[node+GROUP]);

					delete reinterpret_cast<group_t<uint>*>(this->data[node+GROUP]);
				}
				this->data[node+GROUP] = 0;
			}
			
			#if !PLAIN_FRB_MATCH
			if(all)
			#endif
			if(this->data[node+CAPTURES]){
				#if FRB_VERBOSE
				printf("-C");
				#endif
				if(! this->deleted.count(this->data[node+CAPTURES])){
					#if FRB_VERBOSE
					printf("#");
					#endif
					this->deleted.insert(this->data[node+CAPTURES]);

					delete reinterpret_cast<capture_t<long int>*>(this->data[node+CAPTURES]);
				}
				// Used in match to detect nodes with possible
				// captures
				#if PLAIN_FRB_MATCH
				this->data[node+CAPTURES] = 0;
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
		// in this->deleted. If they are not in this->deleted,
		// delete the pointer.
		for(std::list<capture_t<long int>*>::iterator it = this->unknown_ptrs.begin(); it != this->unknown_ptrs.end(); ++it){
			T ptr = reinterpret_cast<T>(*it);
			if(this->deleted.count(ptr))
				continue;
			
			delete *it;

			this->deleted.insert(ptr);
		}
		this->unknown_ptrs.clear();

		#if FRB_VERBOSE
		printf("\n###\n\n");
		#endif
	}

	std::string str(const uint node=char_length){
		std::string result = "[";

		#if FRB_VERBOSE
		printf("Seen ");
		bool seen = false;
		#endif
		for(uint lett = control_positions; lett < char_length; ++lett){
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
	
	const char* c_str(const uint node=char_length){
		return this->str(node).c_str();
	}
  
	// This function analizes a regex expression, and divides it
	// in groups of characters, separating capture groups, expressions
	// and basic char strings.
	inline char** _analize(const char* c_raw_expr){
		#if FRB_VERBOSE
		printf("\nAnalizing pattern: \"%s\"\n", c_raw_expr);
		#endif
		if(! this->analizer_generated)
			this->generate_regex_analizer();

		// The list with the processed substrings
		std::list<std::string>* storage = new std::list<std::string>{c_raw_expr};

		{
		std::smatch match;
		uint last;
		std::string expr_part;

		// Iterate over the expression, looking for regex
		// patterns. If there is one, add it to expression
		for(const auto& [matcher, flags] : this->regex_analizer){
			#if FRB_VERBOSE
			/*
			if(storage->size()){
				printf("[~] ");

				for(std::string &s : *storage){
					if(s.front() > 31)
						printf("%s, ", s.c_str());
					else
						printf("#, ");
				}

				printf("\n");
			}
			*/
			printf("%s\n  ", matcher.pattern.c_str());
			int found = 0;
			int parts = 0;
			#endif

			for(std::list<std::string>::iterator expr_iter = storage->begin(); expr_iter != storage->end();){				
				if((*expr_iter)[0] < 32){
					#if FRB_VERBOSE
					printf("#");
					#endif

					++expr_iter;
					
					continue;
				}

				#if FRB_VERBOSE
				if(!found)
					printf("|");
				#endif

				// Keep this so that we can match the
				// regex again against the suffix of the
				// same loop
				expr_part = *expr_iter;

				bool matched = false;
				while(std::regex_search(expr_part, match, matcher)) {
					matched = true;

					#if FRB_VERBOSE
					if(! found)
						printf(" %s:", (*expr_iter).c_str());
					#endif

					// New prefix string to be added in storage
					std::string prefix = match.prefix().str();
					// New matched string to be added in storage
					// where the first char will be changed to
					// the appropiate identifier
					std::string match_result = "0";
					if(match.size() > 1){
						auto m = match.cbegin() + 1;
						match_result.append(*m);

						#if FRB_VERBOSE
						printf(" [ M:%s ", (*m).str().c_str());
						#endif

						while(++m != match.cend()){
							match_result.append(1, ANALIZE_SEPARATE);

							match_result.append(*m);

							#if FRB_VERBOSE
							printf("M:%s ", (*m).str().c_str());
							#endif
						}
					} else {
						#if FRB_VERBOSE
						printf("[ ");
						#endif
					}

					// New suffix string to be added in storage
					std::string suffix = match.suffix().str();

					// Detect the exact match found
					#define search_char (*(match_result.begin()+1))
					auto find = flags.find(search_char);
					if(find != flags.end()){
						#if FRB_VERBOSE
						++found;
						#endif
					} else {
						find = flags.find('_');
						if(find != flags.end()){
							#if FRB_VERBOSE
							++found;
							#endif
						} else {
							printf("\n[-] Wrong match Idk how\n");
							printf("\t{P:%s c:%s S:%s}\n", prefix.c_str(), search_char, suffix.c_str());
						}
					}
					
					// Change the initial char to the identifier
					match_result[0] = find->second;

					// Replace the matched string with the
					// prefix of the match
					if(prefix.length()){
						#if FRB_VERBOSE
						printf("P:%s ", prefix.c_str());
						#endif

						(*expr_iter).assign(prefix);
						++expr_iter;

						storage->emplace(expr_iter, match_result);
					} 
					// or if it does not exist, replace it
					// with the matched result instead.
					else {
						(*expr_iter).assign(match_result);
						++expr_iter;
					}

					if(suffix.length()){
						storage->emplace(expr_iter, suffix);

						#if FRB_VERBOSE
						printf("S:%s ", suffix.c_str());
						#endif

						expr_part = suffix;
					}
					// No need to continue the loop
					else {
						break;
					}
				}
				if(! matched){
					++expr_iter;
				}
				else {
					#if FRB_VERBOSE
					printf("N:%d ] ", storage->size());
					#endif
				}
			}

			#if FRB_VERBOSE
			if(found)
				printf("\n");
			else
				printf("\r");
			#endif
		}
		}

		char** c_final = new char*[storage->size()];
		char** final_iter = c_final;

		#if FRB_VERBOSE
		printf("\n    FINAL EXPRESSION [%d]:\n  ", storage->size());
		#endif
		for(std::list<std::string>::const_iterator storage_iter = storage->cbegin();
						storage_iter != storage->cend(); ++final_iter, ++storage_iter){
			*final_iter = new char[(*storage_iter).length()+1];
			strcpy(*final_iter, (*storage_iter).c_str());

			#if FRB_VERBOSE
			if((*storage_iter).front() > 31)
				printf("%s, ", (*storage_iter).c_str());
			else
				printf("#%d, ", (*storage_iter).front());

			#endif
		}
		#if FRB_VERBOSE
		printf("\n\n");
		#endif

		delete storage;


		return c_final;
	}

	inline void generate_regex_analizer(){
		// I will not use Mreg to analyze the regex, because
		// in case anything changes, I want to have a slower-safer
		// way to do rebuild the tree.

		#if FRB_VERBOSE
		printf("  Looks like the regex analizer was not generated.\n\tGenerating regex analizer\n");
		#endif

		using umap = std::unordered_map<char, uint>;

		this->regex_analizer = std::vector<std::pair<regex, umap>>{
				// Analizes [^...]
				{regex("(?!\\\\)\\[\\^(.+?)(?!\\\\)\\]"),umap{
					{'_',an_not_sq_brack}
				}},
				// Analizes [...]
				{regex("(?!\\\\)\\[(.+?)(?!\\\\)\\]"),umap{
					{'_',an_sq_brack}
				}},

				// Analizes {m,n}
				{regex("(?!\\\\)\\{(\\d+),(\\d+)(?!\\\\)\\}"),umap{
					{'_',an_bb_brack_m_n}
				}},
				// Analizes {,n}
				{regex("(?!\\\\)\\{,(\\d+)(?!\\\\)\\}"),umap{
					{'_',an_bb_brack__n}
				}},
				// Analizes {m,}
				{regex("(?!\\\\)\\{(\\d+),(?!\\\\)\\}"),umap{
					{'_',an_bb_brack_m_}
				}},
				// Analizes {m}
				{regex("(?!\\\\)\\{(\\d+)(?!\\\\)\\}"),umap{
					{'_',an_bb_brack_m}
				}},

				// Analizes a*? and a+?
				{regex("(?!\\\\)([*+])\\?"),umap{
					{'*',an_asterisk_question},
					{'+',an_plus_question}
				}},
				// Analizes a*, a+ and a?
				{regex("(?!\\\\)([*+?])"),umap{
					{'*',an_asterisk},
					{'+',an_plus},
					{'?',an_question}
				}},

				// Analizes \d, \D, \s, \S, \w, \W, \n, \t, \0
				{regex("\\\\([dDsSwWrt0])"),umap{
					{'_',an_backw_slash}
				}},

				// Analizes . ( )
				{regex("(?!\\\\)([.()])"), umap{
					{'.',an_dot},
					{'(',an_start_paren},
					{')',an_end_paren}
				}}
		};

		this->analizer_generated = true;
	}

  	void append(const char* expression){
		// Delete any invalid pointers from
		// last append
		this->delete_pointers();


		// Any char after a backslash
		bool backslash = false;

		std::stack<uint> depth;
		std::stack<uint> last_nodes;

		uint node = char_length;

		// Calculate expression length
		uint expression_length = 100;
		if(expression_length > this->max_str_size){
			this->max_str_size = expression_length;

			//this->nodes_captures.reserve(expression_length*this->added_id*2);
			//this->str_captures.reserve(expression_length*this->added_id*2);
			//this->str_starts.reserve(expression_length*this->added_id*2);

			this->data[MAX_REG_LENGTH] = expression_length;
		}
		this->contains_captures.push_back(false);

		while(*expression){
			switch (*expression){
				// char '('
				case '(': 
					if(! backslash){
						#if FRB_VERBOSE
						printf("Detected capture to be opened\n");
						#endif
						this->capture.push(1);
						break;
					}
					[[fallthrough]];
				// char ')'
				case ')': 
					if(! backslash){
						#if FRB_VERBOSE
						printf("Detected capture to be closed\n");
						#endif
						this->capture.push(2);
						break;
					}
					[[fallthrough]];
				// char '[' to ']'
				case '[':
					if(! backslash){
						last_nodes.push(node);

						#if FRB_VERBOSE
						printf("Detected squared expression\n");
						#endif
						node = this->append_process_sq(node, &expression);
						break;
					}
					[[fallthrough]];
				// char ']' has no special behaviour
				// char '{' to '}'
				case '{':
					if(! backslash){
						last_nodes.push(node);
						
						#if FRB_VERBOSE
						printf("Detected bubbled expression\n");
						#endif
						node = this->append_process_bbl(node, &expression);
						break;
					}
					[[fallthrough]];
				// char '}'  has no special behaviour

				// char '*'
				case '*':
					if(!backslash){
						#if FRB_VERBOSE
						printf("Detected asterisk expression\n");
						#endif
						node = this->append_asterisk(node, last_nodes.top(), expression);
						break;
					}
					[[fallthrough]];
				// char '+'
				case '+': 
					if(!backslash){
						#if FRB_VERBOSE
						printf("Detected plus expression\n");
						#endif
						
						this->append_plus(node, expression-1);

						break;
					}
					[[fallthrough]];
				// char '?'
				case '?':
					if(!backslash){
						#if FRB_VERBOSE
						printf("Detected question mark expression\n");
						#endif
						
						node = this->append_question_mark(node, last_nodes.top());

						break;
					}
					[[fallthrough]];

				// char '\'
				case '\\':
					backslash = !backslash;

					// if backslash was false, it means
					// next char is special, so no need
					// to add it, get next char
					if(backslash) {
						break;
					}
					[[fallthrough]];
				// char '|'
				case '|':
					// If it's an or, 
					if(! backslash){
						if(this->data[node+GROUP_ID] != this->added_id){
							if(this->data[node+GROUP]){
								this->deleted.insert(this->data[node+GROUP]);

								delete reinterpret_cast<group_t<uint>*>(this->data[node+GROUP]);
							}
							
							uint next = node;
							node = last_nodes.top();
							
							this->data[node+NEXT] = reinterpret_cast<T>(
															static_cast<long int>(next));
							this->data[node+GROUP_ID] = reinterpret_cast<T>(
															static_cast<long int>(this->added_id));
							this->data[node+GROUP] = reinterpret_cast<T>(
															new group_t<uint> {node});
							#if FRB_VERBOSE
							printf(" %ld <- %ld\n", node, next);
							#endif
						}
						#if FRB_VERBOSE
						printf("Detected or expression. Branch out back from node %ld\n", node);
						#endif

						break;
					}
					[[fallthrough]];

				case '.':
					if(! backslash){
						last_nodes.push(node);

						#if FRB_VERBOSE
						printf("Detected dot expression\n");
						#endif
						node = this->append_letters(node, reg_dot, expression+1);
						break;
					}
					[[fallthrough]];
					
				[[likely]] 
				default: 
					last_nodes.push(node);
					#if FRB_VERBOSE
						uint last_id = node;
					#endif

					if(backslash && isalpha(*expression)){
						#if FRB_VERBOSE
							printf("Detected backslash expression \\%c\n", *expression);
						#endif
						node = this->append_backslash(node, expression);
					}
					else{
						#if FRB_VERBOSE
							printf("Detected letter %c\n", *expression);
						#endif
						node = this->append_letter(node, expression);
					}

					backslash = false;
			}
			
			++expression;
		}	

		// End of string
		if(this->data[node+GROUP_ID] == this->added_id){
			group_t<uint>* group = reinterpret_cast<group_t<uint>*>(this->data[node+GROUP]);

			#if FRB_VERBOSE
				printf("Detected final multi-regex node %u of length %u\n", node, group->size());
			#endif
			for(group_t<uint>::const_iterator n = group->cbegin(); n != group->end(); ++n){
				this->data[(*n)+FINAL] = this->added_id;
				
				#if FRB_VERBOSE
					printf("%u,",*n); 
				#endif
			}
			#if FRB_VERBOSE
			printf("\n");
			#endif
		}
		else{
			this->data[node+FINAL] = this->added_id;
		}


		for(size_t cap = this->capture.size(); cap; --cap){
			if(this->capture.back() == 2)
				this->end_group(node);

			this->capture.pop();
		}

		#if FRB_VERBOSE
			printf("Added new expression in node %u {%u}\n", node, this->added_id);
		#endif

		++this->data[NUM_ADDED];
		++this->added_id;

		this->data[SIZE] = this->data.size();
	} 

	// Append inline sub-functions
	inline uint append_letter(const uint node, const char* expr, bool regexpr=false, const uint to=0){
		// If not regexpr we can be sure it has been part of a loop or branching
		// And so, right now, it has just ended
		if(!regexpr){ [[likely]]
			// Count the amount of letters seen
			//(*this->count)[*expr]++;

			// If exists a GROUP_ID and it is the same as this append (every expr append has
			// a unique ID) it means last letter append was actually a charset, and we must
			// converge them all to one
			if(this->data[node+GROUP_ID] == this->added_id){
				uint result = this->data[node+NEXT];
				
				group_t<uint>* group = reinterpret_cast<group_t<uint>*>(this->data[node+GROUP]);

				#if FRB_VERBOSE
					printf("Detected post multi-regex node %u of length %i\n", node, group->size());
				#endif
				for(group_t<uint>::const_iterator n = group->cbegin(); n != group->end(); ++n){
					this->data[*n+*expr+char_offset] = result;
					#if FRB_VERBOSE
					printf(" %u -> %u\n", (*n), result);
					#endif
				}

				return result;
			}
		}
		# if FRB_VERBOSE
		else
			printf("Found clean append_letter (prolly after charset)\n");
		#endif

		// Si ya existe dicha letra, avanza con el
		// objeto al siguiente array.
		if(this->data[node+*expr+char_offset]){
			return append_letter_exist(node, expr);
		}
		else {
			return append_letter_no_exist(node, expr, to);
		}
	}

	inline uint append_letter_exist(const uint node, const char* expr){
		#if FRB_VERBOSE
		printf("Letter exists\n");
		#endif
		// Next node to go
		uint lett = this->data[node+*expr+char_offset];
		
		#if FRB_VERBOSE
		if(lett)
			printf("Next node has %li links\n", this->data[lett+LINKS]);
		#endif

		// Si el objeto estaba apuntado por un charset,
		// duplica el nodo, pues los charset no van a seguir
		// el mismo camino
		if((*(expr+1) != '\\' || this->data[lett+*(expr+1)+char_offset])
					&& this->data[lett+LINKS] > 1){
			return this->copy(node, *expr);
		}
		else{
			capture_t<long int>* capture_merge = new capture_t<long int>();

			// Cast lett+CAPTURE and node+CAPTURE to capture_t<long int>*, and merge
			// them into capture_merge.
			capture_t<long int>* merged_capture;
			
			if(this->data[node+CAPTURES]){
				merged_capture = reinterpret_cast<capture_t<long int>*>(this->data[node+CAPTURES]);

				if(!this->deleted.count(this->data[node+CAPTURES]))
					capture_merge->insert(capture_merge->end(), merged_capture->begin(), merged_capture->end());
			}
			if(this->data[node+CAPTURES]){
				merged_capture = reinterpret_cast<capture_t<long int>*>(this->data[lett+CAPTURES]);

				if(!this->deleted.count(this->data[node+CAPTURES]))
					capture_merge->insert(capture_merge->end(), merged_capture->begin(), merged_capture->end());
			
				if(this->data[lett+LINKS] == 1)
					delete merged_capture;
				else
					// Add capture to unknown_ptrs
					this->unknown_ptrs.push_back(merged_capture);
			}

			if(capture_merge->size())
				this->data[lett+CAPTURES] = reinterpret_cast<T>(capture_merge);
			else
				delete capture_merge;
		}

		#if FRB_VERBOSE
		printf("%u -> %u\n", node, lett);
		#endif
		return lett;
	}

	inline uint append_letter_no_exist(const uint node, const char* expr, const uint to=0){
		#if FRB_VERBOSE
		printf("Letter does not exist");
		#endif
		if(to){
			#if FRB_VERBOSE
			printf(" (shared)\n%u -> %u\n", node, to);
			#endif
			this->add(node, *expr, to);

			return to;
		}
		#if FRB_VERBOSE
		printf("\n");
		#endif
		return this->generate(node,*expr);
	}

	inline uint append_letters(const uint node, const std::string expr, const char* next, const uint to=0){
		uint new_reg, seen_reg, new_arr, existing_node;
		group_t<uint>* group;

		if(to && this->data[to+GROUP])
			group = reinterpret_cast<group_t<uint>*>(this->data[to+GROUP]);
		else		 
		 	group = new group_t<uint>();

		group->reserve(group->size()+expr.length());

		// Common node for all letters that do not exist
		if(to){
			seen_reg = new_arr = to;
		} else if(this->data[node+NEXT])
			seen_reg = new_arr = this->data[node+NEXT];
		else {
			seen_reg = this->data.size();
			this->new_node();
			new_arr = this->data.size();
			this->new_node();
		}

		#if FRB_VERBOSE
		printf("Append of letters \"%s\"\n", expr.c_str());
		#endif

		std::unordered_map<uint, uint> exist_common {};
		std::unordered_map<uint, uint>::const_iterator exists;
		exist_common.reserve(expr.length());

		for(const char* letts = expr.c_str(); *letts; ++letts){
			// If node+letts has no existing node, add to the new node
			if(!(existing_node = this->data[node+*letts+char_offset])){
				#if FRB_VERBOSE
				printf(" - '%c' not exist\n %i -> %i\n", *letts, node, seen_reg);
				#endif
				this->add(node, *letts, seen_reg);
			} else {
				#if FRB_VERBOSE
				printf(" - '%c' exist\n", *letts);
				#endif
				// Find if any other lett has the same node pointing to it
				exists = exist_common.find(existing_node);
				
				// If there isn't (no shared node), duplicate the node
				if(exists == exist_common.end()){
					new_reg = this->append_letter_exist(node, std::string({*letts, *next}).c_str());
					this->data[new_reg+GROUP_ID] = this->added_id;
					this->data[new_reg+GROUP] = reinterpret_cast<T>(group);
					this->data[new_reg+NEXT] = new_arr;
					
					group->insert(new_reg);
					exist_common[existing_node] = new_reg;
				}
				else {
					// If any letter has been seen to go to the same node,
					// go to it too. Note: any duplication has already
					// been done.
					#if FRB_VERBOSE
					printf("Letter exists (shared)\n");
					#endif
					this->add(node, *letts, exists->second);
				}
				#if FRB_VERBOSE
				printf("%i -> %i\n", node, new_reg);
				#endif
			}
		}

		// If any of the letters did not exist, we add the common node
		if(this->data[seen_reg+LINKS]){
			this->data[seen_reg+GROUP_ID] = this->added_id;
			this->data[seen_reg+GROUP] = reinterpret_cast<T>(group);
			this->data[seen_reg+NEXT] = new_arr;
			this->data[seen_reg+CAPTURES] = this->data[node+CAPTURES];
			
			group->insert(seen_reg);

			this->check_capture(seen_reg);

			#if FRB_VERBOSE
			printf("Shared node has %i links\n", this->data[seen_reg+LINKS]);
			#endif

			return seen_reg;
		}

		this->check_capture(new_reg);

		return new_reg;
	}

	inline uint append_backslash(const uint node, const char* expr, uint to=0){
		if(this->data[node+NEXT])
			to = this->data[node+NEXT];

		switch(*expr){
			case 'd':
				return this->append_letters(node, reg_d, expr+1, to);
			case 'w':
				return this->append_letters(node, reg_w, expr+1, to);
			case 'n':
				return this->append_letter(node, std::string({reg_n, *(expr+1)}).c_str(), false, to);
			case 't':
				return this->append_letter(node, std::string({reg_t, *(expr+1)}).c_str(), false, to);
			case 'r':
				return this->append_letter(node, std::string({reg_r, *(expr+1)}).c_str(), false, to);
			case '0':
				return this->append_letter(node, std::string({reg_z, *(expr+1)}).c_str(), false, to);
			case 's':
				return this->append_letters(node, reg_s, expr+1, to);

			// cases on caps, inverse

			default:
				printf("\n### Wrong regex construction \\%c in \"%s\"\n\n", *expr, expr);
				throw std::invalid_argument("Wrong regex construction \\"+*expr);
		}
	}

	uint append_process_sq(const uint node, const char** expr){
		std::string letts = "";
		const char* expression = *expr;
		++expression;
		uint dist = 0;

		bool backslash = false;
		for(; *expression && *expression != ']'; ++expression){
			if(!backslash){
				if(*expression == '\\'){
					backslash = true;
					continue;
				}
				if(*expression == '-'){
					++expression;
					
					if(*expression == '\\')
						++expression;
					else if(*expression == ']')
						break;

					for(int let = letts.back()+1; let <= *expression; ++let)
						letts.push_back(let);
					continue;
				}
			} else 
				backslash = false;

			letts.push_back(*expression);
		}

		*expr = *expr+std::distance(*expr, expression);

		std::unordered_set<char> uniq_letts(letts.begin(), letts.end());

		return this->append_letters(node, 
					std::string(uniq_letts.begin(), uniq_letts.end()), 
					expression+1);
	}

	inline uint append_process_bbl(uint node, const char** expr){
			bool both = false;
			uint min = 0, max = 0;

			std::string buffer = "";
			const char* iter = *expr;
			char it_char, letter = *((*expr)-1);
			
			#if FRB_VERBOSE
			printf("expr: %c{", *((*expr)-1));
			#endif

			while((it_char=*(++iter)) != '}'){
				#if FRB_VERBOSE
				printf("%c", it_char);
				#endif
				if(it_char != ',') [[likely]]
					if(isdigit(it_char)) [[likely]]
						buffer += it_char;
					else
						throw std::invalid_argument("wrong values passed between squared brackets {}");
				else{
					min = std::stoi(buffer);
					both = true;
					buffer.erase();
				}
			}

			*expr = (*expr)+std::distance(*expr, iter);
			max = buffer!="" ? std::stoi(buffer) : 0;

			/* Result:
				· max, min > 0:
					from min to max
				· min = 0:
					max times
				· max = 0
					from min to infinity
			*/

			#if FRB_VERBOSE
			printf("}\n");
			#endif

			if (max == 0){
				#if FRB_VERBOSE
				printf(" %u to infinity the letter %c\n", min, letter);
				#endif

				// Add the minimum letters to start the loop
				for(; min > 1; --min)
					node = this->append_letter(node, (std::string(min, letter)+**expr).c_str());

				// Loop forever if the given letter is found
				this->append_letter(node, std::string(3, letter).c_str(), false, node);

			} 
			else if(min != 0){
				#if FRB_VERBOSE
				printf(" %u to %u times the letter %c\n", min, max, letter);
				#endif

				// Removee one from min, since the first node has already
				// been added
				min -= 1;
				uint diff = max-min;

				uint new_arr = this->data.size();
				this->new_node();

				group_t<uint>* group = new group_t<uint>();
				group->reserve(diff);

				// Get minimum letters found to allow continue matching
				for(; min > 1; --min)
					node = this->append_letter(node, (std::string(min, letter)+**expr).c_str());

				// Add the max-min remaining nodes with exits at any point to the same node
				for(; diff; --diff){
					node = this->append_letter(node, (std::string(diff, letter)+**expr).c_str());
					
					group->insert(node);
				}


				#if FRB_VERBOSE
				printf("Added to group nodes: {");
				#endif
				for(uint reg : *group){
					this->data[reg+GROUP_ID] = this->added_id;
					this->data[reg+GROUP] = reinterpret_cast<T>(group);
					this->data[reg+NEXT] = new_arr;

					#if FRB_VERBOSE
					printf("%u, ", reg);
					#endif
				}
				#if FRB_VERBOSE
				printf("}\n");
				#endif

			} 
			else{
				#if FRB_VERBOSE
				printf(" %u times the letter %c\n", max, letter);
				#endif

				// Removee one from max, since the first node has already
				// been added
				max -= 1;

				for(; max; --max)
					node = this->append_letter(node, (std::string(max, letter)+**expr).c_str());
			}

			return node;
		}
	
	inline uint append_question_mark(uint node, uint last){
		uint next = this->data.size();
		this->new_node();

		group_t<uint>* group, * last_group;
		
		if(this->data[node+GROUP_ID] != this->added_id || !this->data[node+GROUP]){
			group = new group_t<uint> {node};

			this->data[node+NEXT] = next;
			this->data[node+GROUP_ID] = this->added_id;
			this->data[node+GROUP] = reinterpret_cast<T>(group);
		}
		else {
			group = reinterpret_cast<group_t<uint>*>(this->data[node+GROUP]);

			for(group_t<uint>::const_iterator n = group->cbegin(); n != group->end(); ++n){
				this->data[*n+NEXT] = next;
			}
		}

		// Add the last non-optional to the group
		if (this->data[last+GROUP_ID] == this->added_id && this->data[last+GROUP]){
			last_group = reinterpret_cast<group_t<uint>*>(this->data[last+GROUP]);
			this->deleted.insert(this->data[last+GROUP]);

			for(group_t<uint>::const_iterator n = last_group->cbegin(); n != last_group->end(); ++n){
				group->insert(*n);

				this->data[*n+NEXT] = next;
				this->data[*n+GROUP_ID] = this->added_id;
				this->data[*n+GROUP] = reinterpret_cast<T>(group);
			}

			delete last_group;
		} else {
			group->insert(last);
			
			this->data[last+NEXT] = next;
			this->data[last+GROUP_ID] = this->added_id;
			this->data[last+GROUP] = reinterpret_cast<T>(group);
		}
		
		
		return last;
	}
	
	inline uint append_asterisk(uint node, uint last, const char* expr){
		this->append_question_mark(node, last);

		uint new_node;

		if(is_regex(expr-1)){
			new_node = this->append_backslash(node, expr-1, node);
		}
		else{
			new_node = this->append_letter_no_exist(node, expr-1, node);
		}

		return last;
	}
	
	inline uint append_plus(uint node, const char* expr){
		uint plus_1 = this->data.size();
		this->new_node();

		group_t<uint>* g_plus;

		if(is_regex(expr)){
			plus_1 = this->append_backslash(node, expr, plus_1);
			this->append_backslash(plus_1, expr, plus_1);

			g_plus = reinterpret_cast<group_t<uint>*>(this->data[plus_1+GROUP]);
		} else {
			plus_1 = this->append_letter(node, expr, plus_1);
			this->append_letter_no_exist(plus_1, expr, plus_1);

			g_plus = new group_t<uint>{plus_1};
			this->data[plus_1+GROUP] = reinterpret_cast<T>(g_plus);
			this->data[plus_1+GROUP_ID] = this->added_id;
		}

		if(this->data[node+GROUP_ID] == this->added_id && this->data[node+GROUP]){
			group_t<uint>* g_node = reinterpret_cast<group_t<uint>*>(this->data[node+GROUP]);
			this->deleted.insert(this->data[node+GROUP]);
		
			for(group_t<uint>::const_iterator n = g_node->cbegin(); n != g_node->end(); ++n){
				g_plus->insert(*n);

				this->data[*n+GROUP] = reinterpret_cast<T>(g_plus);
				this->data[*n+GROUP_ID] = this->added_id;
			}

			delete g_node;
		} else {
			g_plus->insert(node);
			this->data[node+GROUP] = reinterpret_cast<T>(g_plus);
			this->data[node+GROUP_ID] = this->added_id;
		}

		return plus_1;
	}
	// Append inline sub-functions

  	inline uint generate(const uint node, const char pos){
		uint new_arr = this->data.size();
		this->new_node();
		#if FRB_VERBOSE
			printf("Generated array [%c %i] {%u -> %u}\n %i -> %i\n", pos, pos, node+pos+char_offset, new_arr, node, new_arr);
		#endif

		add(node, pos, new_arr);
		return new_arr;
	}

	inline void new_node(){
		this->data.insert(this->data.end(), char_length, 0);
	}

	inline void add(const uint node, const char pos, const uint new_arr){
		this->data[new_arr+LINKS]++;
		
		this->data[node+pos+char_offset] = new_arr;

		this->check_capture(new_arr);
	}

	void check_capture(const uint node){
		for(size_t cap = this->capture.size(); cap; --cap){
			if(this->capture.back() == 1)
				this->start_group(node);
			else
				this->end_group(node);

			this->capture.pop();
		}
	}

	inline uint copy(const uint node, const char pos){
		uint copied = this->data[node+pos+char_offset];
		uint new_arr = this->data.size();
		this->new_node();
		#if FRB_VERBOSE
		printf("Copied array in %u[%c %i] {%u from %u}\n Letters: ", node, pos, pos, new_arr, copied);
		#endif

		//auto data_ptr = std::find_if(this->data.begin()+copied+control_positions,
		//							this->data.begin()+copied+char_length,fnull);
		// to optimize
		//uint last = last_char - std::distance(
		//			this->data.rbegin(),
		//			std::find_if(copied->data.rbegin(),copied->data.rend(),fnull));

		// Add the following letters(nodes) from the original
		auto data_ptr = this->data.begin()+copied+control_positions;
		//for(uint pos_val = std::distance(this->data.begin()+copied+control_positions, data_ptr)+copied+control_positions; 
		for(auto pos_val = control_positions;
							pos_val < char_length; ++pos_val, ++data_ptr){
			if(*data_ptr){
				#if FRB_VERBOSE
				printf("%c{%u}, ", pos_val-char_offset, *data_ptr);
				#endif
				this->data[new_arr+pos_val] = *data_ptr;
			}
		}
		#if FRB_VERBOSE
		bool copied_data[control_positions];
		#endif

		// Add the data from the original
		uint pos_val = 0;
		for(; pos_val < control_positions; ++pos_val){
			#if FRB_VERBOSE
				if(this->data[new_arr+pos_val] = this->data[copied+pos_val])
					copied_data[pos_val] = true;
			#else
				this->data[new_arr+pos_val] = this->data[copied+pos_val];
			#endif
		}
		#if FRB_VERBOSE
		printf("\n Data: ");
		for(uint c_data_pos = 0; c_data_pos < control_positions; ++c_data_pos)
			if(copied_data[c_data_pos])
				printf("%u, ", c_data_pos);
		printf("\n");
		#endif

		this->data[copied+LINKS]--;

		this->data[node+pos+char_offset] = new_arr;

		return new_arr;
	}
  
	inline void start_group(const uint node){
		if(!this->data[node+CAPTURES]){
				this->data[node+CAPTURES] = reinterpret_cast<T>(
												new capture_t<long int>()
											);
		}

		if(this->data[node+GROUP_ID] == this->added_id && this->data[node+GROUP]){
			// Open the capture in the group of generated nodes
			group_t<uint>* group = reinterpret_cast<group_t<uint>*>(this->data[node+GROUP]);

			#if FRB_VERBOSE
			printf("Opening %d captures\n", group->size());
			#endif
			for(group_t<uint>::const_iterator n = group->cbegin(); n != group->end(); ++n)
				if(!this->data[(*n)+CAPTURES]){
					this->data[(*n)+CAPTURES] = reinterpret_cast<T>(
												new capture_t<long int> {this->added_id}
												);
					#if FRB_VERBOSE
					printf("\tCAPTURES %u : 0x%x\n", (*n), this->data[(*n)+CAPTURES]);
					#endif
				}
				else
					reinterpret_cast<capture_t<long int>*>(this->data[(*n)+CAPTURES])
									->push_back(this->added_id);
		}
		else{
			reinterpret_cast<capture_t<long int>*>(this->data[node+CAPTURES])
							->push_back(this->added_id);
			#if FRB_VERBOSE
			printf("\tCAPTURE START %u : 0x%x\n", node, this->data[node+CAPTURES]);
			#endif
		}

		this->contains_captures[this->added_id] = true;
	}

	inline void end_group(const uint node){
		if(!this->data[node+CAPTURES]){
			this->data[node+CAPTURES] = reinterpret_cast<T>(
											new capture_t<long int>()
										);
			#if FRB_VERBOSE
			printf("\tCAPTURES %u : 0x%x\n", node, this->data[node+CAPTURES]);
			#endif
		}


		if(this->data[node+GROUP_ID] == this->added_id && this->data[node+GROUP]){
			// Close the capture in the group of generated nodes
			group_t<uint>* group = reinterpret_cast<group_t<uint>*>(this->data[node+GROUP]);
		
			#if FRB_VERBOSE
			printf("Closing %d captures\n", group->size());
			#endif
			for(group_t<uint>::iterator n = group->begin(); n != group->end(); ++n){
				reinterpret_cast<capture_t<long int>*>(this->data[node+CAPTURES])
							->push_front(-this->added_id);
							
				#if FRB_VERBOSE
				printf("\tCAPTURES %u : 0x%x\n", (*n), this->data[(*n)+CAPTURES]);
				#endif
			}
		}
		else{
			reinterpret_cast<capture_t<long int>*>(this->data[node+CAPTURES])
							->push_front(-this->added_id);
			#if FRB_VERBOSE
			printf("\tCAPTURE END %u : 0x%x\n", node, this->data[node+CAPTURES]);
			#endif
		}

	}

	void clean(){
		// Breath, hash and remove 
		
		std::unordered_map<T, uint> capture_data_start = std::unordered_map<T, uint>();
		std::unordered_map<uint, uint> capture_data_space = std::unordered_map<uint, uint>();
		const size_t max_size = this->data.size();
	
		#if FRB_VERBOSE
		printf("\n\n### FRB_CLEANING\n");
		#endif

		uint capture_cell;

		for(uint node = char_length; node != max_size; node += char_length){
			// If the node has a capture vector
			// and it is a pointer (gt data.size())
			if(this->data[node+CAPTURES]){
				if(this->data[node+CAPTURES] > static_cast<uint>(this->data.size())){
					// If we have not deleted this ptr yet
					if(! this->deleted.count(this->data[node+CAPTURES])){
						capture_t<long int>* captures = reinterpret_cast<capture_t<long int>*>(this->data[node+CAPTURES]);
						
						captures->sort();
						captures->reverse();

						this->deleted.insert(this->data[node+CAPTURES]);

						std::unordered_map<uint, uint>::iterator spaces_iter = capture_data_space.begin();

						for(; spaces_iter != capture_data_space.end(); ++spaces_iter){
							// Space_left + captures.size + 1 <= char_length
							if(spaces_iter->second+captures->size() < char_length)
								break;
						} 


						#if FRB_VERBOSE
						printf("\tNew ptr 0x%X in node %u\n\t Assigned to ", this->data[node+CAPTURES], node);
						#endif

						if(spaces_iter == capture_data_space.end()){
							capture_cell = this->data.size();
							this->new_node();
							this->nodes_data_captures.insert(capture_cell);

							#if FRB_VERBOSE
							printf("NEW generated ");
							#endif


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
						printf("node %u\n\t Contains %zu capture nodes\n\t  [", capture_cell, captures->size());
						#endif
						
						capture_data_start[this->data[node+CAPTURES]] = capture_cell;
						this->data[capture_cell] = captures->size();

						// Take note the new direction assigned
						this->data[node+CAPTURES] = capture_cell;

						for(long int captured_node : *captures){
							++capture_cell;
							this->data[capture_cell] = captured_node;
							#if FRB_VERBOSE
							printf(" %d[%u]", captured_node, capture_cell);
							#endif
						}

						#if FRB_VERBOSE
						printf(" ]\n");
						#endif

						delete captures;
					}
					// If we deleted it, access to the capture cell in the umap
					else {
						typename
						std::unordered_map<T, uint>::const_iterator seen_cell = 
								capture_data_start.find(this->data[node+CAPTURES]);

						if(seen_cell != capture_data_start.cend()){
							this->data[node+CAPTURES] = seen_cell->second;

							#if FRB_VERBOSE
							printf("\tSeen ptr 0x%X in node %u\n\t Redirected to %u\n", 
										this->data[node+CAPTURES], node, seen_cell->second);
							#endif
						} else {
							printf("[!]\n[!] ERROR: Missing ptr in %u (0x%x)\n[!]\n\n\n", node, this->data[node+CAPTURES]);
							this->data[node+CAPTURES] = 0;
						}
					}
				}
			}
		}
		#if FRB_VERBOSE
		printf("### Size %zu -> %zu\n\n", max_size, this->data.size());
		#endif
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

	static inline intptr_t load_position(std::istream& in_stream, uint pos){
		#if FRB_VERBOSE
		printf("Loading position %i of data\n", pos);
		#endif

		std::vector<intptr_t> positions = std::vector<intptr_t>();

		in_stream.read(reinterpret_cast<char *>(positions.data()), pos * sizeof(intptr_t));

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

		for(uint node = char_length; node != max_size; node += char_length){
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
				// Return to node % char_length = 0
				node -= node % char_length;
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

	inline uint count_sorted(uint node, const uint value)
		__attribute__ ((const))
		#if !FRB_PROFILE
		__attribute__ ((always_inline))
		#endif
		__attribute__ ((hot))
	{
		#if FRB_VERBOSE
		printf("CS[%u,%d|%u]:", node, this->data[node], value);
		#endif
		const uint end = node + this->data[node] + 1;

		++node;
		if(this->data[node] > value){
			#if FRB_VERBOSE
			printf(" - None\n");
			#endif
			return 0;
		}
		++node;

		uint result = 0;
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

	inline uint count_sorted_backw(uint node, const uint value)
		__attribute__ ((const))
		#if !FRB_PROFILE
		__attribute__ ((always_inline))
		#endif
		__attribute__ ((hot))
	{
		#if FRB_VERBOSE
		printf("CSB[%u,%d|%u]:", node, this->data[node], value);
		#endif
		const uint end = node;
		const uint max = this->added_id + 1;
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

		uint result = 0;
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

	uint match(const char * str)
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
		uint mreg = char_length;

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
		__builtin_prefetch(&this->data[char_length+CAPTURES]);

		#if !PLAIN_FRB_MATCH
		// If contains any captures in the initial node
		if(this->data[mreg+CAPTURES]){
			#if FRB_VERBOSE
			printf("Detected captures in node %u [%X]\n", mreg, this->data[mreg+CAPTURES]);
			
			restart_str.push_back(*str);
			#endif	
			this->nodes_captures.push_back(this->data[mreg+CAPTURES]);
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
			if(this->data[mreg+CAPTURES]){
				#if FRB_VERBOSE
				printf("Detected captures in node %u [%u]\n", mreg, this->data[mreg+CAPTURES]);
			
				restart_str.push_back(*str);
				#endif
				this->nodes_captures.push_back(this->data[mreg+CAPTURES]);
				this->str_captures.push_back(str);
			}
			#endif

			++str;
		}

		const uint final = this->data[mreg+FINAL];

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

			uint starting_captures = 0;
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

			uint starts = 0;
			for(; starting_captures; --starting_captures, ++starts)
				this->str_starts.push_back(*str_iter);
			
			std::string buffer = std::string();
			const char* group_start;
			char *subStr;

			uint new_groups, char_dist;

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
		uint mreg = char_length;

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
		__builtin_prefetch(&this->data[char_length+CAPTURES]);

		#if !PLAIN_FRB_MATCH
		// If contains any captures in the initial node
		if(this->data[mreg+CAPTURES]){
			#if FRB_VERBOSE
			printf("Detected captures in node %u [%X]\n", mreg, this->data[mreg+CAPTURES]);
			
			restart_str.push_back(*str);
			#endif	
			this->nodes_captures.push_back(this->data[mreg+CAPTURES]);
			this->str_captures.push_back(str);
		}
		#endif

		do{
			while(mreg = this->data[mreg+*str+char_offset]){
				#if FRB_VERBOSE
				printf("match %c (%i)\n", *str, *str);
				
				printf("%u -> %u\n", last_id, mreg);
				last_id = mreg;
				#endif
				
				#if !PLAIN_FRB_MATCH
				if(this->data[mreg+CAPTURES]){
					#if FRB_VERBOSE
					printf("Detected captures in node %u [%u]\n", mreg, this->data[mreg+CAPTURES]);
				
					restart_str.push_back(*str);
					#endif
					this->nodes_captures.push_back(this->data[mreg+CAPTURES]);
					this->str_captures.push_back(str);
				}
				#endif

				if(! *(++str))
					goto end_str;
			}
		} while(1);

		end_str:

		const uint final = this->data[mreg+FINAL];

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

			uint starting_captures = 0;
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

			uint starts = 0;
			for(; starting_captures; --starting_captures, ++starts)
				this->str_starts.push_back(*str_iter);
			
			std::string buffer = std::string();
			const char* group_start;
			char *subStr;

			uint new_groups, char_dist;

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


int main(int argc, char* argv[])
{
	#if FRB_GENERATE
	// add to be matched
	std::vector<const char*> add = {
						"hola\\s?", "hombr(\\w)s", "hombr\\w", 
						"adios", "adioses", "\\d+",
						"hola\\.", "[Gg]uap[oae]",
						"[b-z1b]@", "\\..\\.", "a\\db",
						"ha{4}h", "l(o{2,})p", "limit{2,5}",
						"aleluy(a*)", "numeros?", "chi(c)(o|a|e)(s+)",
						"(Hola, )?(mi )?amigo!", "muy (buenas)?",
						"(muchas )*gracias", "pues( si)*",
						"tu( sabes)+", "(no, )+mola"
						};
	# endif

	#if FRB_MATCH
	// to be checked if they match (not all must match)
	std::vector<const char*> match {
						"hombros", "adios", "hombree", 
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
						"muy ", "muy buenas", "muybuenas",
						"buenas", "gracias", "muchas gracias",
						"muchas muchas muchas gracias",
						"pues", "pues si", "pues si si si",
						"tu sabes", "tu sabes sabes sabes", "tu",
						"no, mola", "no, no, no, mola", "mola",
						"muchas   gracias", "pues siii",
						"tu sabesssss", "no,    mola", 
						"muchasgracias", "no,mola"
						};

	// Ids start by 1 from the add array, since id=0 means no match
	std::vector<uint> id {
						2, 4, 0, 3, 2,
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

	std::fstream file;

	#if FRB_GENERATE
	Mreg<intptr_t> r = Mreg<intptr_t>();
	r._analize("H*?ol\\da*[abvde]{1,2}*?");

    auto add_regex_start = Clock::now();
	// To be optimized
	for(const char* added : add){
		#if FRB_VERBOSE
		printf("\n\n###\n");
		#if !FRB_CLEAN
		printf("Added string \"%s\" of id %u\n", added, r.added_id);
		#endif
		#endif
		r.append(added);
	}
    auto add_regex_end = Clock::now();

	r.delete_pointers();

	#if !FRB_CLEAN
	// Print after timing for performace reasons.
	// Done in reverse to simplify correct added_id print
	#if !FRB_VERBOSE
	for(uint r_added = 1; r_added < add.size()+1; ++r_added)
		printf("Added string \"%s\" of id %u\n", add[add.size()-r_added], r.added_id-r_added);
	printf("\n\n");
	#endif
	printf("\n\n[?] End of append.\nResult (starting node):\n%s\nResult (size): %u\n\n\nMatching:\n", 
				r.c_str(), r.data.size());
	#endif

	r.clean();

	#if FRB_STORE
    /*  Open the language JSON file as a fstream */
    file.open("FRB.tree", std::ios::out);

	store_data_start = Clock::now();
	r.store(file);
	store_data_end = Clock::now();

	file.close();
	#endif

	#else
	file.open("FRB.tree", std::ios::in);

	#define POSITION_SIZE 5

	#if POSITION_SIZE == 4
		Mreg<uint_fast16_t> r = Mreg<uint_fast16_t>();
	#elif POSITION_SIZE == 5
		Mreg<uint_fast32_t> r = Mreg<uint_fast32_t>();
	#elif POSITION_SIZE == 6
		Mreg<uint_fast64_t> r = Mreg<uint_fast64_t>();
	#else
		Mreg<uint_fast8_t> r = Mreg<uint_fast8_t>();
	#endif

	file.close();

    /*  Open the language JSON file as a fstream */
    file.open("FRB.tree", std::ios::in);
	
	load_data_start = Clock::now();
	r.load(file);
	load_data_end = Clock::now();

	file.close();
	#endif

	#if FRB_MATCH

	#if !FRB_VERBOSE
	// So that it appears in profiling:
	for(const char* match_str : match){
		r.match(match_str);
	}
	#endif

	std::vector<uint> match_ids {};
	match_ids.reserve(match.size());

	uint correct = 0, missed = 0, missmatched = 0;
	uint found;

	const uint match_size = static_cast<uint>(match.size());
	uint check = 0;

    auto match_regex_start = Clock::now();
	for(const char* match_str : match){
		#if FRB_VERBOSE
			found = r.match(match_str);

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
			match_ids.push_back(r.match(match_str));
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
	#if FRB_GENERATE
	std::chrono::nanoseconds add_time = std::chrono::duration_cast<std::chrono::nanoseconds>(
										add_regex_end-add_regex_start);
	std::chrono::nanoseconds store_time = std::chrono::duration_cast<std::chrono::nanoseconds>(
										store_data_end-store_data_start);

	std::cout << " Compilation ("<< add.size() <<" ex) : " << add_time.count() <<" ns.\n";
	std::cout << " Compilation  (Avg.) : "<< add_time.count()/add.size() <<" ns.\n";
	std::cout << " Data storage : " << store_time.count() <<" ns.\n";
	
	#endif

	#if FRB_MATCH
	std::chrono::nanoseconds match_time = std::chrono::duration_cast<std::chrono::nanoseconds>(
										match_regex_end-match_regex_start);
	#if !FRB_GENERATE
	std::chrono::nanoseconds load_time = std::chrono::duration_cast<std::chrono::nanoseconds>(
										load_data_end-load_data_start);

	std::cout << " Data loading : " << load_time.count() <<" ns.\n";
	#endif
	std::cout << " Matching ("<< match.size() <<" regex) : "<< match_time.count() <<" ns.\n";
	std::cout << " Matching     (Avg.) : "<< match_time.count()/match.size() <<" ns.\n";
	#endif

	printf("#################\n");
	#endif

	return 0;
}

#endif