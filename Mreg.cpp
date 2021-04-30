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
#include <iostream>

#define VERBOSE false

// Define the positions in data of some useful info
// The id of the node
#define ID 0
// The final id of the match. 0 if the node is not final
#define FINAL 1
//
#define GROUP_ID 2
//
#define GROUP 3
//
#define NEXT 4

// If performance over memory, control_positions = first_char
#define first_char  32
#define last_char 127
#define control_positions 32

#define char_offset control_positions - first_char

#define char_length last_char - first_char + control_positions

#define b_node std::array<void*,char_length>

#define reg_d std::string("0123456789")
#define reg_w reg_d+std::string("ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz")
#define reg_n '\n'
#define reg_t '\t'
#define reg_r '\r'
#define reg_z '\0'
#define reg_s {' ',reg_n,reg_t}
#define reg_dot reg_w+reg_s

const inline bool fnull(void* p){ return p != nullptr; }

class Mreg{
	private:
		uint* expr_id;
		uint* added_id;

		std::unique_ptr<uint> add_ptr;

	public:
		// In a future, they will be private
		std::array<uint, char_length>* count = new std::array<uint, char_length>();
		std::array<uint, char_length>* storage = new std::array<uint, char_length>();
		
  
  //uint expr;
//  uint added;
 
		b_node data;
	
		uint length;
		uint id;

		uint links = 0;
  
  
	Mreg(uint* expr_id=nullptr, uint* added_id=nullptr, uint links=1) {
		#if VERBOSE
			//printf("0const\n");
		#endif
		this->data = b_node();
		this->length = 0;

		this->links = links;
		
		#if VERBOSE
			//printf("1const\n");
		#endif
		
		this->data.fill(nullptr);
		
		//if(expr_id)
		this->expr_id = expr_id;
		//  else{
		//   this->expr = 1;
		//   this->expr_id = &this->expr;
		//  }
		#if VERBOSE
			//printf("2const\n");
		#endif
		//  if(added_id)
		this->added_id = added_id;
		//  else{
		//   this->added = 1;
		//   this->added_id = &this->added;
		//  }  
		#if VERBOSE
			//printf("3const\n");
		#endif
		
		this->id = ++(*expr_id);
		this->data[ID] = &this->id;
		#if VERBOSE
			//printf("4const\n");
		#endif
	}

	std::string str(){
		std::string result = "[";
		for(uint lett = first_char; lett < last_char; lett++){
			if(this->data[lett] != nullptr)
				result += {lett, ',', ' '};
		}
		return result.substr(0, result.length()-2) + ']';
	}

	const char* c_str(){
		return this->str().c_str();
	}
  
  	inline void append(const char* expression){
		// Setup of vars
		// Starting regex_object
		Mreg* reg_obj = this;
		// Clear any counter of chars
		this->count->fill(0);
		// and clear any stored counter
		this->storage->fill(0);

		// Any char after a backslash
		bool backslash = false;

		//Mreg* lett;
		std::stack<Mreg*> depth;

		

		while(*expression){
			switch ((*expression)+char_offset){
				
				// char '('
				case '(':
				// char ')'
				case ')':
				// char '[' to ']'
				case '[':
					if(! backslash){
						//charset = true;
						this->append_process_sq(reg_obj, &expression);
						continue;
					}
				// char ']' has no special behaviour
				// char '{' to '}'
				case '{':
					if(! backslash){
						//bubbled = true;
						this->append_process_bbl(reg_obj, &expression);
						continue;
					}
				// char '}'  has no special behaviour


				// char '*'
				case '*':
				// char '+'
				case '+':
				// char '?'
				case '?':

				// char '\'
				case '\\':
					backslash = !backslash;

					// if backslash was false, it means
					// next char is special, so no need
					// to add it, get next char
					if(backslash) {
						break;
					}
				// char '|'
				case '|':


				default:		
					#if VERBOSE
						uint last_id = reg_obj->id;
						printf("Detected ");
					#endif

					if(backslash && isalpha(*expression)){
						#if VERBOSE
							printf("backslash expression \\%c\n", *expression);
						#endif
						reg_obj = this->append_backslash(reg_obj, expression);
					}
					else{
						#if VERBOSE
							printf("letter %c\n", *expression);
						#endif
						reg_obj = this->append_letter(reg_obj, expression);
					}
					#if VERBOSE
						printf("%u -> %u\n", last_id, reg_obj->id);
					#endif

					backslash = false;
			}
			expression++;
		}	
		
		// End of string
		if(reg_obj->data[GROUP_ID] && *((int*) reg_obj->data[GROUP_ID]) == (*this->added_id)+1){
			std::vector<Mreg*> group = *((std::vector<Mreg*>*) reg_obj->data[GROUP]);
			
			int* final_id = new int(++(*this->added_id));

			#if VERBOSE
				printf("Detected final multi-regex node %u of length %i\n", reg_obj->id, group.size());
			#endif
			for(std::vector<Mreg*>::iterator v = group.begin(); v != group.end(); v++){
				(*v)->data[FINAL] = final_id;
			}
		}
		else
			reg_obj->data[FINAL] = new int(++(*this->added_id));

		#if VERBOSE
			printf("Added new expression in %u {%u}\n", reg_obj->id, *this->added_id);
		#endif
	} 

	// Append inline sub-functions
		inline Mreg* append_letter(Mreg* reg_obj, const char* expr, bool regexpr=false){
			if(!regexpr){
				(*this->count)[*expr]++;

				if(reg_obj->data[GROUP_ID] && *((int*) reg_obj->data[GROUP_ID]) == (*this->added_id)+1){
					Mreg* result = (Mreg*) reg_obj->data[NEXT];
					
					std::vector<Mreg*> group = *((std::vector<Mreg*>*) reg_obj->data[GROUP]);

					#if VERBOSE
						printf("Detected post multi-regex node %u of length %i\n", reg_obj->id, group.size());
					#endif
					for(std::vector<Mreg*>::iterator v = group.begin(); v != group.end(); v++){
						(*v)->data[*expr] = result;
					}
					result->length++;

					return result;
				}
			}

			Mreg* lett = (Mreg*) reg_obj->data[*expr];

			// Si ya existe dicha letra, avanza con el
			// objeto al siguiente array.
			if(lett){
				// Si el objeto estaba apuntado por un charset,
				// duplica el nodo, pues los charset no van a seguir
				// el mismo camino
				if(*(expr+1) != '\\' && lett->data[*(expr+1)] != nullptr && lett->links > 1){
					return reg_obj->copy(*expr);
				}
				#if VERBOSE
				printf("%u -> %u\n", reg_obj->id, lett->id);
				#endif
				return lett;
			}
			else {
				return reg_obj->generate(*expr);
			}
		}

		inline Mreg* append_letters(Mreg* reg_obj, const std::string expr, const char next){
			Mreg* new_reg, *new_arr = new Mreg(this->expr_id, this->added_id, expr.length());
			std::vector<Mreg*>* group = new std::vector<Mreg*>();
			group->reserve(expr.length());

			for(const char* letts = expr.c_str(); *letts; letts++){
				new_reg = this->append_letter(reg_obj, std::string({*letts, next}).c_str());
				new_reg->data[GROUP_ID] = new int((*this->added_id)+1);
				new_reg->data[GROUP] = (void*) group;
				new_reg->data[NEXT] = (void*) new_arr;

				group->push_back(new_reg);
			}

			return new_reg;
		}

		inline Mreg* append_backslash(Mreg* reg_obj, const char* expr){
			switch(*expr){
				case 'd':
					return this->append_letters(reg_obj, reg_d, *(expr+1));
				case 'w':
					return this->append_letters(reg_obj, reg_w, *(expr+1));
				case 'n':
					return this->append_letter(reg_obj, std::string({reg_n, *(expr+1)}).c_str());
				case 't':
					return this->append_letter(reg_obj, std::string({reg_t, *(expr+1)}).c_str());
				case 'r':
					return this->append_letter(reg_obj, std::string({reg_r, *(expr+1)}).c_str());
				case '0':
					return this->append_letter(reg_obj, std::string({reg_z, *(expr+1)}).c_str());
				case 's':
					return this->append_letters(reg_obj, reg_s, *(expr+1));

				// cases on caps, inverse

				default:
					throw std::invalid_argument("Wrong regex construction \\"+*expr);
			}
		}

		inline Mreg* append_process_sq(Mreg* reg_obj, const char** expr){

		}

		inline void append_process_bbl(Mreg* reg_obj, const char** expr){
			bool both = false;
			uint min = 0, max = 0;

			std::string buffer = "";
			const char* iter = *expr;
			char letter;
			
			while((letter=*(iter++)) != '}'){
				if(letter != ',')
					if(isdigit(letter))
						buffer += letter;
					else
						throw std::invalid_argument("wrong values passed between squared brackets {}");
				else{
					min = std::stoi(buffer);
					both = true;
					buffer.erase();
				}
			}

			max = std::stoi(buffer);
		}
  
  	inline Mreg* generate(const char pos, uint links=1){
		Mreg* new_arr = new Mreg(this->expr_id, this->added_id, links);
		#if VERBOSE
			printf("Generated array in %u[%c %i] {%u}\n", this->id, pos, pos, new_arr->id);
		#endif
		
		this->length++;
		
		this->data[pos] = new_arr;
		return new_arr;
	}

	inline Mreg* copy(const char pos, uint links=1){
		Mreg* copied = (Mreg*) this->data[pos];
		Mreg* new_arr = new Mreg(this->expr_id, this->added_id, links);
		#if VERBOSE
			printf("Copied array in %u[%c %i] {%u from %u}\n", this->id, pos, pos, new_arr->id, copied->id);
		#endif

		auto data_ptr = std::find_if(copied->data.begin()+first_char,copied->data.end(),fnull);
		uint last = last_char - std::distance(
					copied->data.rbegin(),
					std::find_if(copied->data.rbegin(),copied->data.rend(),fnull));

		for(uint pos_val = std::distance(copied->data.begin(), data_ptr); 
							pos_val != last; pos_val++, data_ptr++){
			if(data_ptr != nullptr){
				new_arr->data[pos_val] = (void*) data_ptr;
				new_arr->length++;
			}
		}

		copied->links--;

		return new_arr;
	}
  
	void clean(){
		// Breath, hash and remove 
		std::hash<std::string> a;
		return;
	}
  
	bool match(const char * str, uint* ret){
		Mreg* mreg = this;
		
		#if VERBOSE
			printf("mat0 %c, 0x%x\n", *str, mreg->data[*str]);
		#endif
		while(*str && mreg->data[*str]){
			#if VERBOSE
				printf("mat %c %i\n", *str, *str);
				uint last_id = mreg->id;
			#endif
			mreg = (Mreg*) mreg->data[*str];
			#if VERBOSE
				printf("%u -> %u\n", last_id, mreg->id);
			#endif
			str++;
		}
		#if VERBOSE
			printf("mat2 - %i", !*str);
		#endif
		
		if(!*str){
			#if VERBOSE
				printf(" - 0x%x\n", mreg->data[FINAL]);
				printf("%s\n",mreg->c_str());
			#endif
			
			if(mreg->data[FINAL]){
				*ret = *(uint*) mreg->data[FINAL];
				return true;
			}
		}
		#if VERBOSE
			printf("\n");
		#endif
		return false;
	}
};


int main(int argc, char *argv[])
{
	// add to be matched
	std::string add[] = {"hola", "hombr\\ws", "hombr\\w", "adios", "adioses", "\\d"};
	// to be checked if they match (not all must match)
	std::string match[] = {"hombros","adios","hombree", "hombro", "hombres", "hola", "dios", "", "1"};
	
	uint ua = 0;
	uint ub = 0;
	
	#if VERBOSE
		printf("#### Start ####\n");
	#endif
	
	Mreg r = Mreg(&ua, &ub);

	for(std::string added : add){
		r.append(added.c_str());
		#ifndef CLEAN
		printf("Added string \"%s\" of id %u\n", added.c_str(), ub);
		#endif
	}
	
	uint* ma = new uint(0); 
	
	bool found;

	#ifndef CLEAN
	printf("\n\n[?] End of append.\nResult (starting node):\n%s\n\n\nMatching:\n", r.c_str());
	#endif
	
	for(std::string check : match){
		found = r.match(check.c_str(), ma);
		
		#if VERBOSE
			printf("%i\n", r.length);
		#endif
		#ifndef CLEAN
		if(found)
			printf("\t [+] Match of \"%s\" [ match id = %u ]\n",check.c_str(),*ma);
		else
			printf("\t [-] Not match of \"%s\"\n", check.c_str());
		#endif
	}
}