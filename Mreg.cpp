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

#define VERBOSE false
#define CLEAN false


// The final id of the match. 0 if the node is not final
#define FINAL 0
//
#define GROUP_ID 1
//
#define GROUP 2
//
#define NEXT 3
// Define the positions in data of some useful info
#define LINKS 4

#define first_char  32
#define last_char 127
#define control_positions 5

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

class Mreg{
	private:
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
	}

	std::string str(const uint node=char_length){
		std::string result = "[";
		for(uint lett = control_positions; lett < char_length; lett++){
			if(this->data[node+lett]){
				#if VERBOSE
				printf("Seen %c in str()\n", lett-char_offset);
				#endif
				result.append(std::string({static_cast<char>(lett-char_offset), ',', ' '}));
			}
		}
		result = result.substr(0, result.length()-2);
		result.append(std::string("]"));
		return result;
	}

	const char* c_str(const uint node=char_length){
		return this->str(node).c_str();
	}
  
  	inline void append(const char* expression){
		// Any char after a backslash
		bool backslash = false;

		//uint lett;
		//std::stack<uint> depth;

		uint node = char_length;

		while(*expression){
			switch (*expression){
				
				// char '('
				case '(': 
					if(! backslash){
						break;
					}
					[[fallthrough]];
				// char ')'
				case ')': 
					if(! backslash){
						break;
					}
					[[fallthrough]];
				// char '[' to ']'
				case '[':
					if(! backslash){
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
					[[fallthrough]];
				// char '+'
				case '+': 
					[[fallthrough]];
				// char '?'
				case '?':
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

				case '.':
					if(! backslash){
						#if VERBOSE
						printf("Detected dot expression\n");
						#endif
						node = this->append_letters(node, reg_dot, expression+1);
						break;
					}
					[[fallthrough]];
					
				[[likely]] 
				default: 
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
			expression++;
		}	

		// End of string
		if(this->data[node+GROUP_ID] == this->added_id){
			std::vector<uint>* group = reinterpret_cast<std::vector<uint>*>(this->data[node+GROUP]);

			#if VERBOSE
				printf("Detected final multi-regex node %u of length %u\n", node, group->size());
			#endif
			for(std::vector<uint>::iterator n = group->begin(); n != group->end(); n++){
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

		#if VERBOSE
			printf("Added new expression in node %u {%u}\n", node, this->added_id);
		#endif

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
				
				std::vector<uint>* group = reinterpret_cast<std::vector<uint>*>(this->data[node+GROUP]);

				#if VERBOSE
					printf("Detected post multi-regex node %u of length %i\n", node, group->size());
				#endif
				for(std::vector<uint>::iterator n = group->begin(); n != group->end(); n++){
					this->data[*n+*expr+char_offset] = result;
					#if VERBOSE
					printf("%u -> %u\n", (*n), result);
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
			printf("Next object has %li links\n", this->data[lett+LINKS]);
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

	inline uint append_letters(const uint node, const std::string expr, const char* next){
		uint new_reg, seen_reg, new_arr, existing_node;
		std::vector<uint>* group = new std::vector<uint>();
		group->reserve(expr.length());

		// Common node for all letters that do not exist
		seen_reg = this->data.size();
		this->new_node();
		new_arr = this->data.size();
		this->new_node();

		#if VERBOSE
		printf("Append of letters \"%s\"\n", expr.c_str());
		#endif

		std::unordered_map<uint, uint> exist_common {};
		std::unordered_map<uint, uint>::const_iterator exists;
		exist_common.reserve(expr.length());

		for(const char* letts = expr.c_str(); *letts; letts++){
			if(!(existing_node = this->data[node+*letts+char_offset])){
				#if VERBOSE
				printf(" - '%c' not exist\n %i -> %i\n", *letts, node, seen_reg);
				#endif
				this->add(node, *letts, seen_reg);
			} else {
				#if VERBOSE
				printf(" - '%c' exist\n", *letts);
				#endif
				exists = exist_common.find(existing_node);
				if(exists == exist_common.end()){
					new_reg = this->append_letter_exist(node, std::string({*letts, *next}).c_str());
					this->data[new_reg+GROUP_ID] = this->added_id;
					this->data[new_reg+GROUP] = reinterpret_cast<intptr_t>(group);
					this->data[new_reg+NEXT] = new_arr;
					
					group->push_back(new_reg);
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
			
			group->push_back(seen_reg);

			#if VERBOSE
			printf("Shared node has %i links\n", this->data[seen_reg+LINKS]);
			#endif

			return seen_reg;
		}

		return new_reg;
	}

	inline uint append_backslash(const uint node, const char* expr){
		switch(*expr){
			case 'd':
				return this->append_letters(node, reg_d, expr+1);
			case 'w':
				return this->append_letters(node, reg_w, expr+1);
			case 'n':
				return this->append_letter(node, std::string({reg_n, *(expr+1)}).c_str());
			case 't':
				return this->append_letter(node, std::string({reg_t, *(expr+1)}).c_str());
			case 'r':
				return this->append_letter(node, std::string({reg_r, *(expr+1)}).c_str());
			case '0':
				return this->append_letter(node, std::string({reg_z, *(expr+1)}).c_str());
			case 's':
				return this->append_letters(node, reg_s, expr+1);

			// cases on caps, inverse

			default:
				throw std::invalid_argument("Wrong regex construction \\"+*expr);
		}
	}

	uint append_process_sq(const uint node, const char** expr){
		std::string letts = "";
		const char* expression = *expr;
		expression++;
		uint dist = 0;

		bool backslash = false;
		for(; *expression && *expression != ']'; expression++){
			if(!backslash){
				if(*expression == '\\'){
					backslash = true;
					continue;
				}
				if(*expression == '-'){
					expression++;
					
					if(*expression == '\\')
						expression++;
					else if(*expression == ']')
						break;

					for(int let = letts.back()+1; let <= *expression; let++)
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
				for(; min > 1; min--)
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

				std::vector<uint>* group = new std::vector<uint>();
				group->reserve(diff);

				// Get minimum letters found to allow continue matching
				for(; min > 1; min--)
					node = this->append_letter(node, (std::string(min, letter)+**expr).c_str());

				// Add the max-min remaining nodes with exits at any point to the same node
				for(; diff > 0; diff--){
					node = this->append_letter(node, (std::string(diff, letter)+**expr).c_str());
					
					group->push_back(node);
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

				for(; max > 0; max--)
					node = this->append_letter(node, (std::string(max, letter)+**expr).c_str());
			}

			return node;
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
							pos_val < char_length; pos_val++, data_ptr++){
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
		for(; pos_val < control_positions; pos_val++){
			#if VERBOSE
				if(this->data[new_arr+pos_val] = this->data[copied+pos_val])
					copied_data[pos_val] = true;
			#else
				this->data[new_arr+pos_val] = this->data[copied+pos_val];
			#endif
		}
		#if VERBOSE
		printf("\n Data: ");
		for(uint c_data_pos = 0; c_data_pos < control_positions; c_data_pos++)
			if(copied_data[c_data_pos])
				printf("%u, ", c_data_pos);
		printf("\n");
		#endif

		this->data[copied+LINKS]--;

		this->data[node+pos+char_offset] = new_arr;

		return new_arr;
	}
  
	void clean(){
		// Breath, hash and remove 
		std::hash<std::string> a;
		return;
	}
  
	uint match(const char * str){
		uint mreg = char_length;
		
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
			str++;
		}
		#if VERBOSE
			printf("mat2 - id: %u\nEnd: %s\n", this->data[mreg+FINAL], this->c_str(mreg));
		#endif

		if((!*str) && this->data[mreg+FINAL])
			return this->data[mreg+FINAL];

		return 0;
	}
};


int main(int argc, char *argv[])
{
	// add to be matched
	std::vector<const char*> add = {
						"hola\\s", "hombr\\ws", "hombr\\w", 
						"adios", "adioses", "\\d",
						"hola\\.", "[Gg]uap[oae]",
						"[b-z1b]@", "\\..\\.", "a\\db",
						"ha{4}h", "lo{2,}p", "limit{2,5}"
						};

	// to be checked if they match (not all must match)
	std::vector<const char*> match {
						"hombros", "adios", "hombree", 
						"hombro", "hombres", "hola ", "a1b",
						"hola.", "dios", "", "1",
						"Guapa", "guape", "guapi",
						"r@", "1@", "a@", "2@",
						".h.", ".@.", "haaaah",
						"haaah", "haaaaah", "loop",
						"looooooop", "lop", "limit",
						"limitt", "limittttt", "limitttttt"
						};

	// Ids start by 1 from the add array, since id=0 means no match
	std::vector<uint> id {
						2, 4, 0, 3, 2,
						1, 11, 7, 0, 0, 
						6, 8, 8, 0, 9, 
						9, 0, 0, 10, 10, 
						12, 0, 0, 13, 13,
						0, 0, 14, 14, 0
						};

	#if VERBOSE
		printf("#### Start ####\n");
	#endif
	
	Mreg r = Mreg();

	typedef std::chrono::high_resolution_clock Clock;
    auto add_regex_start = Clock::now();
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
	for(uint r_added = 1; r_added < add.size()+1; r_added++)
		printf("Added string \"%s\" of id %u\n", add[add.size()-r_added], r.added_id-r_added);
	#endif
	//printf("\n\n[?] End of append.\nResult (starting node):\n%s\n\n\nMatching:\n", r.c_str());
	#endif
	
	std::vector<uint> match_ids {};
	match_ids.reserve	(match.size());

	float correct = 0;
	uint found;

    auto match_regex_start = Clock::now();
	for(uint check = 0; check < match.size(); check++){
		#if VERBOSE
			found = r.match(match[check]);

			if(found){
				printf("\t [%c] Match of \"%s\" [ match id = %u ]\n",
									(id[check]==found)?'+':'-',match[check],found);
				if(id[check]==found)
					correct++;
			}
			else{
				printf("\t [%c] Not match of \"%s\"\n",
									(id[check]==0)?'+':'-', match[check]);
				if(id[check]==0)
					correct++;
			}
		#else
			match_ids.push_back(r.match(match[check]));
		#endif
	}
    auto match_regex_end = Clock::now();

	#if !CLEAN
	#if !VERBOSE
	for(uint check = 0; check < match.size(); check++){
		found = match_ids[check];
		
		if(found){
			printf("\t [%c] Match of \"%s\" [ match id = %u ]\n",
								(id[check]==found)?'+':'-',match[check],found);
			if(id[check]==found)
				correct++;
		}else{
			printf("\t [%c] Not match of \"%s\"\n",
								(id[check]==0)?'+':'-', match[check]);
			if(id[check]==0)
				correct++;
		}
	}
	#endif

	printf("\n#### RESULTS ####\n");

	printf("  %.1f%% of correct matches.\n", correct*100/match.size());

	#if VERBOSE
	printf("\n[!] WARNING: Prints enabled. Expect performance regression.");
	#endif
	printf("\n#### TIMINGS ####\n");
	std::chrono::nanoseconds add_time = std::chrono::duration_cast<std::chrono::nanoseconds>(
										add_regex_end-add_regex_start);
	std::chrono::nanoseconds match_time = std::chrono::duration_cast<std::chrono::nanoseconds>(
										match_regex_end-match_regex_start);
	std::cout << " Compilation ("<< add.size() <<" ex) : " << add_time.count() <<" ns.\n";
	std::cout << " Compilation  (Avg.) : "<< add_time.count()/add.size() <<" ns.\n";
	std::cout << " Matching ("<< match.size() <<" regex) : "<< match_time.count() <<" ns.\n";
	std::cout << " Matching     (Avg.) : "<< match_time.count()/match.size() <<" ns.\n";

	printf("#################\n");
	#endif
}