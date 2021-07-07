#include <array>
#include <string>
#include <memory>
#include <unordered_map>
#include <unordered_set>
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

#define VERBOSE false
#define CLEAN false
#define GENERATE false
#define STORE true
#define MATCH true


// The final id of the match. 0 if the node is not final
#define FINAL 0
// The id of the added match string, to not 
// mistake groups that are from previous compilations
#define GROUP_ID 1
// A pointer to a vector<uint> of nodes, from which 
// we were meant to merge, when we advance one char
#define GROUP 2
// The next node we must route to
#define NEXT 3
// The amount of nodes pointing to this node
#define LINKS 4
// A pointer to a list of captures to keep track what
// sub-strings to get and what not
#define CAPTURES 5

// Nodes in data [0 : char_length] used to aid
// in performance with pre-calculated statistics
//
// The number of added_id in the tree
#define NUM_ADDED 1
// The maximum length of a regex expression
#define MAX_LENGTH 2

#define group_t std::unordered_set
#define capture_t std::list

#define first_char  32
#define last_char 127
#define control_positions 7
#define reserved_data_size 16384

#define char_offset (control_positions - first_char)

#define char_length (last_char - first_char + control_positions)

#define reg_d std::string("0123456789")
#define reg_w reg_d+std::string("ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz")
#define reg_n '\n'
#define reg_t '\t'
#define reg_r '\r'
#define reg_z '\0'
#define reg_s std::string({' ',reg_n,reg_t})
#define reg_dot reg_w+reg_s+std::string("!@#$%^&*()_+{}[]'\\|\"/-=>?<ºª`~")

inline bool fnull(uint p){ return p != 0; }
inline bool is_regex(const char* expr){
	return *(expr-1) == '\\' && !(*(expr-1) == '\\' && ! isalpha(*expr));
}
inline uint count_sorted(const uint* expr, uint value){
	uint result = 0;
	while(*expr){
		if(*expr == value){
			++result;
			++expr;
			break;
		}
		++expr;
	}

	if(!result) return 0;

	while(*expr == value){
		++result;
		++expr;
	}

	return result;
}

// TODO: Change all pointers to proper C++ ptr
class Mreg{
	private:
		// Maybe turn into vector<vector<array<2, int>>> ?
		// vector [match]
		// vector [capture]
		// array [id, char*] (id < 0 means capture end)
		std::vector<std::vector<std::array<intptr_t,2>>> _capture_groups = 
								std::vector<std::vector<std::array<intptr_t,2>>>{
									std::vector<std::array<intptr_t,2>>()
								};
		std::vector<std::vector<const char*>> match_groups = std::vector<std::vector<const char*>>();
		std::vector<std::vector<bool>> match_endings = std::vector<std::vector<bool>>();

		std::vector<uint> nodes_captures = std::vector<uint>();
		std::vector<const char*> str_captures = std::vector<const char*>();

		std::queue<uint8_t> capture = std::queue<uint8_t>();
		// Also, I could turn CAPTURES to int and add the ids only.
		// capture end would be in last capture node + 1
	
		uint max_str_size = 0;

	public:
		uint added_id=1;
		// In a future, they will be private
		//std::array<uint, char_length>* count = new std::array<uint, char_length>();
		//std::array<uint, char_length>* storage = new std::array<uint, char_length>();

		// This will take the form of void* in positions 0..control_positions
		// and of int in control_positions+1..char_length
		std::vector<intptr_t> data;
  
  
	Mreg() {
		this->data = std::vector<intptr_t>(char_length*2, 0);
		this->data.reserve(reserved_data_size);
	}


	std::string str(const uint node=char_length){
		std::string result = "[";

		#if VERBOSE
		printf("Seen ");
		bool seen = false;
		#endif
		for(uint lett = control_positions; lett < char_length; ++lett){
			if(this->data[node+lett]){
				#if VERBOSE
				printf("%c ", lett-char_offset);
				seen = true;
				#endif
				result.append(std::string({static_cast<char>(lett-char_offset), ',', ' '}));
			}
		}
		#if VERBOSE
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
  
  	void append(const char* expression){
		// Any char after a backslash
		bool backslash = false;

		std::stack<uint> depth;
		std::stack<uint> last_nodes;

		uint node = char_length;

		this->_capture_groups.push_back(std::vector<std::array<intptr_t,2>>());

		// Calculate expression length
		uint expression_length = 100;
		if(expression_length > this->max_str_size){
			this->max_str_size = expression_length;

			this->nodes_captures.reserve(expression_length*this->added_id);
			this->str_captures.reserve(expression_length*this->added_id);

			this->data[MAX_LENGTH] = expression_length;
		}

		while(*expression){
			switch (*expression){
				// char '('
				case '(': 
					if(! backslash){
						this->capture.push(1);
						break;
					}
					[[fallthrough]];
				// char ')'
				case ')': 
					if(! backslash){
						this->capture.push(2);
						break;
					}
					[[fallthrough]];
				// char '[' to ']'
				case '[':
					if(! backslash){
						last_nodes.push(node);

						#if VERBOSE
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
						
						#if VERBOSE
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
						#if VERBOSE
						printf("Detected asterisk expression\n");
						#endif
						node = this->append_asterisk(node, last_nodes.top(), expression);
						break;
					}
					[[fallthrough]];
				// char '+'
				case '+': 
					if(!backslash){
						#if VERBOSE
						printf("Detected plus expression\n");
						#endif
						
						this->append_plus(node, expression-1);

						break;
					}
					[[fallthrough]];
				// char '?'
				case '?':
					if(!backslash){
						#if VERBOSE
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
							uint next = node;
							node = last_nodes.top();
							
							this->data[node+NEXT] = reinterpret_cast<intptr_t>(
															static_cast<long int>(next));
							this->data[node+GROUP_ID] = reinterpret_cast<intptr_t>(
															static_cast<long int>(this->added_id));
							this->data[node+GROUP] = reinterpret_cast<intptr_t>(
															new group_t<uint> {node});
							#if VERBOSE
							printf(" %ld <- %ld\n", node, next);
							#endif
						}
						#if VERBOSE
						printf("Detected or expression. Branch out back from node %ld\n", node);
						#endif

						break;
					}
					[[fallthrough]];

				case '.':
					if(! backslash){
						last_nodes.push(node);

						#if VERBOSE
						printf("Detected dot expression\n");
						#endif
						node = this->append_letters(node, reg_dot, expression+1);
						break;
					}
					[[fallthrough]];
					
				[[likely]] 
				default: 
					last_nodes.push(node);
					#if VERBOSE
						uint last_id = node;
					#endif

					if(backslash && isalpha(*expression)){
						#if VERBOSE
							printf("Detected backslash expression \\%c\n", *expression);
						#endif
						node = this->append_backslash(node, expression);
					}
					else{
						#if VERBOSE
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

			#if VERBOSE
				printf("Detected final multi-regex node %u of length %u\n", node, group->size());
			#endif
			for(group_t<uint>::iterator n = group->begin(); n != group->end(); ++n){
				this->data[(*n)+FINAL] = this->added_id;
				
				#if VERBOSE
					printf("%u,",*n); 
				#endif
			}
			#if VERBOSE
			printf("\n");
			#endif
		}
		else{
			this->data[node+FINAL] = this->added_id;
		}


		for(size_t cap = this->capture.size(); cap > 0; --cap){
			if(this->capture.back() == 2)
				this->end_group(node);

			this->capture.pop();
		}

		#if VERBOSE
			printf("Added new expression in node %u {%u}\n", node, this->added_id);
		#endif

		//
		std::vector<const char*> gr = std::vector<const char*>();
		std::vector<bool> endings = std::vector<bool>();

		gr.reserve(this->_capture_groups[this->added_id].capacity());
		endings.reserve(this->_capture_groups[this->added_id].capacity());

		this->match_groups.push_back(gr);
		this->match_endings.push_back(endings);
		//

		++this->data[NUM_ADDED];
		++this->added_id;
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

				#if VERBOSE
					printf("Detected post multi-regex node %u of length %i\n", node, group->size());
				#endif
				for(group_t<uint>::iterator n = group->begin(); n != group->end(); ++n){
					this->data[*n+*expr+char_offset] = result;
					#if VERBOSE
					printf(" %u -> %u\n", (*n), result);
					#endif
				}

				return result;
			}
		}
		# if VERBOSE
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
		#if VERBOSE
		printf("Letter exists\n");
		#endif
		// Next node to go
		uint lett = this->data[node+*expr+char_offset];
		
		#if VERBOSE
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
		#if VERBOSE
		printf("%u -> %u\n", node, lett);
		#endif
		return lett;
	}

	inline uint append_letter_no_exist(const uint node, const char* expr, const uint to=0){
		#if VERBOSE
		printf("Letter does not exist");
		#endif
		if(to){
			#if VERBOSE
			printf(" (shared)\n%u -> %u\n", node, to);
			#endif
			this->add(node, *expr, to);

			return to;
		}
		#if VERBOSE
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

		#if VERBOSE
		printf("Append of letters \"%s\"\n", expr.c_str());
		#endif

		std::unordered_map<uint, uint> exist_common {};
		std::unordered_map<uint, uint>::const_iterator exists;
		exist_common.reserve(expr.length());

		for(const char* letts = expr.c_str(); *letts; ++letts){
			// If node+letts has no existing node, add to the new node
			if(!(existing_node = this->data[node+*letts+char_offset])){
				#if VERBOSE
				printf(" - '%c' not exist\n %i -> %i\n", *letts, node, seen_reg);
				#endif
				this->add(node, *letts, seen_reg);
			} else {
				#if VERBOSE
				printf(" - '%c' exist\n", *letts);
				#endif
				// Find if any other lett has the same node pointing to it
				exists = exist_common.find(existing_node);
				
				// If there isn't (no shared node), duplicate the node
				if(exists == exist_common.end()){
					new_reg = this->append_letter_exist(node, std::string({*letts, *next}).c_str());
					this->data[new_reg+GROUP_ID] = this->added_id;
					this->data[new_reg+GROUP] = reinterpret_cast<intptr_t>(group);
					this->data[new_reg+NEXT] = new_arr;
					
					group->insert(new_reg);
					exist_common[existing_node] = new_reg;
				}
				else {
					// If any letter has been seen to go to the same node,
					// go to it too. Note: any duplication has already
					// been done.
					#if VERBOSE
					printf("Letter exists (shared)\n");
					#endif
					this->add(node, *letts, exists->second);
				}
				#if VERBOSE
				printf("%i -> %i\n", node, new_reg);
				#endif
			}
		}

		// If any of the letters did not exist, we add the common node
		if(this->data[seen_reg+LINKS] > 0){
			this->data[seen_reg+GROUP_ID] = this->added_id;
			this->data[seen_reg+GROUP] = reinterpret_cast<intptr_t>(group);
			this->data[seen_reg+NEXT] = new_arr;
			
			group->insert(seen_reg);

			#if VERBOSE
			printf("Shared node has %i links\n", this->data[seen_reg+LINKS]);
			#endif

			return seen_reg;
		}

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
			
			#if VERBOSE
			printf("expr: %c{", *((*expr)-1));
			#endif

			while((it_char=*(++iter)) != '}'){
				#if VERBOSE
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

			#if VERBOSE
			printf("}\n");
			#endif

			if (max == 0){
				#if VERBOSE
				printf(" %u to infinity the letter %c\n", min, letter);
				#endif

				// Add the minimum letters to start the loop
				for(; min > 1; --min)
					node = this->append_letter(node, (std::string(min, letter)+**expr).c_str());

				// Loop forever if the given letter is found
				this->append_letter(node, std::string(3, letter).c_str(), false, node);

			} 
			else if(min != 0){
				#if VERBOSE
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
				for(; diff > 0; --diff){
					node = this->append_letter(node, (std::string(diff, letter)+**expr).c_str());
					
					group->insert(node);
				}


				#if VERBOSE
				printf("Added to group nodes: {");
				#endif
				for(uint reg : *group){
					this->data[reg+GROUP_ID] = this->added_id;
					this->data[reg+GROUP] = reinterpret_cast<intptr_t>(group);
					this->data[reg+NEXT] = new_arr;

					#if VERBOSE
					printf("%u, ", reg);
					#endif
				}
				#if VERBOSE
				printf("}\n");
				#endif

			} 
			else{
				#if VERBOSE
				printf(" %u times the letter %c\n", max, letter);
				#endif

				// Removee one from max, since the first node has already
				// been added
				max -= 1;

				for(; max > 0; --max)
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
			this->data[node+GROUP] = reinterpret_cast<intptr_t>(group);
		}
		else {
			group = reinterpret_cast<group_t<uint>*>(this->data[node+GROUP]);

			for(group_t<uint>::iterator n = group->begin(); n != group->end(); ++n){
				this->data[*n+NEXT] = next;
			}
		}

		// Add the last non-optional to the group
		if (this->data[last+GROUP_ID] == this->added_id && this->data[last+GROUP]){
			last_group = reinterpret_cast<group_t<uint>*>(this->data[last+GROUP]);

			for(group_t<uint>::iterator n = last_group->begin(); n != last_group->end(); ++n){
				group->insert(*n);

				this->data[*n+NEXT] = next;
				this->data[*n+GROUP_ID] = this->added_id;
				this->data[*n+GROUP] = reinterpret_cast<intptr_t>(group);
			}
		} else {
			group->insert(last);
			
			this->data[last+NEXT] = next;
			this->data[last+GROUP_ID] = this->added_id;
			this->data[last+GROUP] = reinterpret_cast<intptr_t>(group);
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

			g_plus = new std::unordered_set<uint>{plus_1};
			this->data[plus_1+GROUP] = reinterpret_cast<intptr_t>(g_plus);
			this->data[plus_1+GROUP_ID] = this->added_id;
		}

		if(this->data[node+GROUP_ID] == this->added_id && this->data[node+GROUP]){
			group_t<uint>* g_node = reinterpret_cast<group_t<uint>*>(this->data[node+GROUP]);
		
			for(group_t<uint>::iterator n = g_node->begin(); n != g_node->end(); ++n){
				g_plus->insert(*n);

				this->data[*n+GROUP] = reinterpret_cast<intptr_t>(g_plus);
				this->data[*n+GROUP_ID] = this->added_id;
			}
		} else {
			g_plus->insert(node);
			this->data[node+GROUP] = reinterpret_cast<intptr_t>(g_plus);
			this->data[node+GROUP_ID] = this->added_id;
		}

		return plus_1;
	}
	// Append inline sub-functions

  	inline uint generate(const uint node, const char pos){
		uint new_arr = this->data.size();
		this->new_node();
		#if VERBOSE
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

		for(size_t cap = this->capture.size(); cap > 0; --cap){
			if(this->capture.back() == 1)
				this->start_group(new_arr);
			else
				this->end_group(new_arr);

			this->capture.pop();
		}
	}

	inline uint copy(const uint node, const char pos){
		uint copied = this->data[node+pos+char_offset];
		uint new_arr = this->data.size();
		this->new_node();
		#if VERBOSE
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
				#if VERBOSE
				printf("%c{%u}, ", pos_val-char_offset, *data_ptr);
				#endif
				this->data[new_arr+pos_val] = *data_ptr;
			}
		}
		#if VERBOSE
		bool copied_data[control_positions];
		#endif

		// Add the data from the original
		uint pos_val = 0;
		for(; pos_val < control_positions; ++pos_val){
			#if VERBOSE
				if(this->data[new_arr+pos_val] = this->data[copied+pos_val])
					copied_data[pos_val] = true;
			#else
				this->data[new_arr+pos_val] = this->data[copied+pos_val];
			#endif
		}
		#if VERBOSE
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
				this->data[node+CAPTURES] = reinterpret_cast<intptr_t>(
											new capture_t<long int>()
											);
		}

		if(this->data[node+GROUP_ID] == this->added_id && this->data[node+GROUP]){
			// Open the capture in the group of generated nodes
			group_t<uint>* group = reinterpret_cast<group_t<uint>*>(this->data[node+GROUP]);

			#if VERBOSE
			printf("Opening %d captures\n", group->size());
			#endif
			for(group_t<uint>::iterator n = group->begin(); n != group->end(); ++n)
				if(!this->data[(*n)+CAPTURES]){
					this->data[(*n)+CAPTURES] = reinterpret_cast<intptr_t>(
												new capture_t<long int> {this->added_id}
												);
					#if VERBOSE
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
			#if VERBOSE
			printf("\tCAPTURE %u : 0x%x\n", node, this->data[node+CAPTURES]);
			#endif
		}
	}

	inline void end_group(const uint node){
		if(!this->data[node+CAPTURES]){
			this->data[node+CAPTURES] = reinterpret_cast<intptr_t>(
											new capture_t<long int>()
										);
			#if VERBOSE
			printf("\tCAPTURES %u : 0x%x\n", node, this->data[node+CAPTURES]);
			#endif
		}


		if(this->data[node+GROUP_ID] == this->added_id && this->data[node+GROUP]){
			// Close the capture in the group of generated nodes
			group_t<uint>* group = reinterpret_cast<group_t<uint>*>(this->data[node+GROUP]);
		
			#if VERBOSE
			printf("Closing %d captures\n", group->size());
			#endif
			for(group_t<uint>::iterator n = group->begin(); n != group->end(); ++n){
				reinterpret_cast<capture_t<long int>*>(this->data[node+CAPTURES])
							->push_front(-static_cast<long int>(this->added_id));
							
				#if VERBOSE
				printf("\tCAPTURES %u : 0x%x\n", (*n), this->data[(*n)+CAPTURES]);
				#endif
			}
		}
		else
			reinterpret_cast<capture_t<long int>*>(this->data[node+CAPTURES])
							->push_front(-static_cast<long int>(this->added_id));

	}

	void clean(){
		// Breath, hash and remove 
		std::hash<std::string> a;
		return;
	}
  
	std::ostream& store(std::ostream& out_stream){
		#if VERBOSE
		printf("Serializing all %zu data pos... ", this->data.size());
		#endif
		
		const size_t data_size = this->data.size();

		out_stream.write(reinterpret_cast<char const*>(&data_size), sizeof(data_size));
		out_stream.write(reinterpret_cast<char const*>(this->data.data()), data_size*sizeof(intptr_t));

		#if !CLEAN || VERBOSE
		printf("[#] Data serialized.\n");
		#endif

		return out_stream;
	}

	std::istream& load(std::istream& in_stream){
		#if VERBOSE
		printf("Loading all");
		#endif

		decltype(this->data.size()) size;
		in_stream.read(reinterpret_cast<char *>(&size), sizeof(size));
		
		#if VERBOSE
		printf("%zu data pos... ", size);
		#endif

		this->data.resize(size);
		in_stream.read(reinterpret_cast<char *>(this->data.data()), this->data.size() * sizeof(intptr_t));

		#if !CLEAN || VERBOSE
		printf("[#] Data deserialized.\n\n");
		#endif

		this->nodes_captures.reserve(this->data[MAX_LENGTH] * this->data[NUM_ADDED]);
		this->str_captures.reserve(this->data[MAX_LENGTH] * this->data[NUM_ADDED]);

		return in_stream;
	}

	uint match(const char * str){
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

		if(this->data[mreg+CAPTURES]){
			#if VERBOSE
			printf("Detected captures in node %u", mreg);
			#endif
			nodes_captures.push_back(mreg);
			str_captures.push_back(str);
		}

		#if VERBOSE
			printf("mat0 %c, 0x%x\n", *str, this->data[mreg+*str+char_offset]);

			uint last_id = mreg;
		#endif
		while(*str && (mreg = this->data[mreg+*str+char_offset])){
			#if VERBOSE
			printf("mat %c %i\n", *str, *str);
			
			printf("%u -> %u\n", last_id, mreg);
			last_id = mreg;
			#endif
			
			if(this->data[mreg+CAPTURES]){
				#if VERBOSE
				printf("Detected captures in node %u", mreg);
				#endif	
				nodes_captures.push_back(mreg);
				str_captures.push_back(str);
			}

			++str;
		}

		const uint final = this->data[mreg+FINAL];

		#if VERBOSE
			printf("mat2 - id: %u\nEnd: %s\n", final, this->c_str(mreg));

		#endif

		if((!*str) && final){ [[likely]];
			#if VERBOSE
			//for

			std::vector<const char*>::const_iterator cap_groups = this->match_groups[final].begin();
			const std::vector<const char*>::const_iterator cap_groups_end = this->match_groups[final].end();
			
			if(cap_groups != cap_groups_end){
				std::string buffer = std::string();
				buffer.reserve(128);
				// Max capture group can only be of size string
				int cap_id; char* sub_str;
				
				std::stack<const char*> starts = std::stack<const char*>();

				std::unordered_set<int> seen = std::unordered_set<int>();

				printf("  Captured groups:\n");
				for(std::vector<bool>::const_iterator cap_endings = this->match_endings[final].begin();
							cap_groups != cap_groups_end; ++cap_groups, ++cap_endings){
					//if(!seen.find())
					
					// if end of capture
					if(*cap_endings && !starts.empty()){
						buffer.clear();
						const int subs_end = std::distance(starts.top(), *cap_groups);

						// It is not necessary right now, could be added as is,
						// but in the future it will, so I do it anyways
						buffer.append(starts.top(), subs_end);

						printf("    %s\n", buffer.c_str());
						starts.pop();

					// if start of capture
					} else 
						starts.push(*cap_groups);
				}
				
				// Get the substring of all missing capture groups from the ptr
				// they were captured from to the end of the string	
				for(int stack_empty = starts.size(); stack_empty > 0; --stack_empty){
					buffer.clear();
					// Substring until the end
					const char* subs_start = starts.top();
					const int subs_end = std::distance(subs_start, str);

					// It is not necessary right now, could be added as is,
					// but in the future it will, so I do it anyways
					buffer.append(starts.top(), subs_end);

					printf("    %s\n", buffer.c_str());
					starts.pop();
				}
				printf("\n");
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
	#if GENERATE
	// add to be matched
	std::vector<const char*> add = {
						"hola\\s?", "hombr(\\w)s", "hombr\\w", 
						"adios", "adioses", "\\d+",
						"hola\\.", "[Gg]uap[oae]",
						"[b-z1b]@", "\\..\\.", "a\\db",
						"ha{4}h", "l(o{2,})p", "limit{2,5}",
						"aleluy(a*)", "numeros?", "chi(c)(o|a|e)(s+)",
						"while\\s*\\(?.*:"
						};
	# endif

	#if MATCH
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
						"while   var1  >  not 10  and var2 == var3   or    3<not 40    :"
						};

	// Ids start by 1 from the add array, since id=0 means no match
	std::vector<uint> id {
						2, 4, 0, 3, 2,
						1, 11, 1, 7, 0, 0, 
						6, 8, 8, 0, 9, 
						9, 0, 0, 10, 10, 
						12, 0, 0, 13, 13,
						0, 0, 14, 14, 0,
						6, 15, 15, 0, 16,
						16, 0, 0, 17, 17,
						17, 0, 0
						};
	#endif

	#if VERBOSE
		printf("#### Start ####\n");
	#endif
	typedef std::chrono::high_resolution_clock Clock;
	std::chrono::_V2::system_clock::time_point load_data_start, load_data_end,
											store_data_start, store_data_end;

	Mreg r = Mreg();	

	#if GENERATE
    auto add_regex_start = Clock::now();
	// To be optimized
	for(const char* added : add){
		#if VERBOSE
		printf("\n\n###\n");
		#if !CLEAN
		printf("Added string \"%s\" of id %u\n", added, r.added_id);
		#endif
		#endif
		r.append(added);
	}
    auto add_regex_end = Clock::now();

	#if !CLEAN
	// Print after timing for performace reasons.
	// Done in reverse to simplify correct added_id print
	#if !VERBOSE
	for(uint r_added = 1; r_added < add.size()+1; ++r_added)
		printf("Added string \"%s\" of id %u\n", add[add.size()-r_added], r.added_id-r_added);
	printf("\n\n");
	#endif
	printf("\n\n[?] End of append.\nResult (starting node):\n%s\nResult (size): %u\n\n\nMatching:\n", 
				r.c_str(), r.data.size());
	#endif

	#if STORE
	{
	std::fstream file;

    /*  Open the language JSON file as a fstream */
    file.open("FBR.tree", std::ios::out);

	store_data_start = Clock::now();
	r.store(file);
	store_data_end = Clock::now();
	}
	#endif

	#else
	{
	std::fstream file;

    /*  Open the language JSON file as a fstream */
    file.open("FBR.tree", std::ios::in);
	
	load_data_start = Clock::now();
	r.load(file);
	load_data_end = Clock::now();

	// FOR PROFILING ONLY
	r.match(match[0]);
	r.match(match[0]);
	// FOR PROFILING ONLY
	}
	#endif

	#if MATCH
	std::vector<uint> match_ids {};
	match_ids.reserve(match.size());

	int correct = 0;
	uint found;

	const uint match_size = static_cast<uint>(match.size());
	uint check = 0;

    auto match_regex_start = Clock::now();
	for(const char* match_str : match){
		#if VERBOSE
			found = r.match(match_str);

			if(found){
				printf("\t [%c] Match of \"%s\" [ match id = %u ]\n",
									(id[check]==found)?'+':'-',match_str,found);
				if(id[check]==found)
					++correct;
			}
			else{
				printf("\t [%c] Not match of \"%s\"\n",
									(id[check]==0)?'+':'-', match_str);
				if(id[check]==0)
					++correct;
			}

			++check;
		#else
			match_ids.push_back(r.match(match_str));
		#endif
	}
    auto match_regex_end = Clock::now();

	#if !CLEAN
	#if !VERBOSE
	printf("Matched %d strings:\n", match.size());

	for(check = 0; check < match.size(); ++check){
		found = match_ids[check];
		
		if(found){
			printf("\t [%c] Match of \"%s\" [ match id = %u ]\n",
								(id[check]==found)?'+':'-',match[check],found);
			if(id[check]==found)
				++correct;
		}else{
			printf("\t [%c] Not match of \"%s\"\n",
								(id[check]==0)?'+':'-', match[check]);
			if(id[check]==0)
				++correct;
		}
	}
	#endif
	#endif

	printf("\n#### RESULTS ####\n");

	#if MATCH
	printf(" (%d/%zu) of correct matches.\n", correct, match.size());
	printf("  %.1f%% of correct matches.\n\n", static_cast<float>(correct*100)/match.size());
	#endif

	printf("  Size of data: %ld\n", r.data.size());

	#if VERBOSE
	printf("\n[!] WARNING: Prints enabled. Expect performance regression.");
	#endif
	printf("\n#### TIMINGS ####\n");
	#if GENERATE
	std::chrono::nanoseconds add_time = std::chrono::duration_cast<std::chrono::nanoseconds>(
										add_regex_end-add_regex_start);
	std::chrono::nanoseconds store_time = std::chrono::duration_cast<std::chrono::nanoseconds>(
										store_data_end-store_data_start);

	std::cout << " Compilation ("<< add.size() <<" ex) : " << add_time.count() <<" ns.\n";
	std::cout << " Compilation  (Avg.) : "<< add_time.count()/add.size() <<" ns.\n";
	std::cout << " Data storage : " << store_time.count() <<" ns.\n";
	
	#endif

	#if MATCH
	std::chrono::nanoseconds match_time = std::chrono::duration_cast<std::chrono::nanoseconds>(
										match_regex_end-match_regex_start);
	#if !GENERATE
	std::chrono::nanoseconds load_time = std::chrono::duration_cast<std::chrono::nanoseconds>(
										load_data_end-load_data_start);

	std::cout << " Data loading : " << load_time.count() <<" ns.\n";
	#endif
	std::cout << " Matching ("<< match.size() <<" regex) : "<< match_time.count() <<" ns.\n";
	std::cout << " Matching     (Avg.) : "<< match_time.count()/match.size() <<" ns.\n";
	#endif

	printf("#################\n");
	#endif
}