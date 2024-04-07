// Do I have to add a self loop on the end CFG location, because then the epsilon equation creates issues
// end node will always be 2
/*
Comments:
	Considering start invariant and neglecting all other invariants, also the start invariant should be a polyhedra(Which I think would not pose a problem)
	https://tapas.labri.fr/wp/wp-content/uploads/2017/02/FAST-manual.pdf
*/
#include <iostream>
#include <algorithm>
#include <cstdio>
#include <vector>
#include <cstring>
#include <sstream>
#include <cctype>
#include <set>
#include <map>
#include <fstream>
#include <deque>
#include <iomanip>
#include <fstream>
#include <queue>
#include <ctime>
#include <sys/time.h>


#include "files/Parser.h"
using namespace std;
#define MAXL 700000 //Maximum length of the program
#define part(x,a,b) (x.substr((a),((b)-(a))))
#define pb push_back
#define A(i,j) (front->affexpr->children[i]->children[0]->expression[j+1])
#define b(i) (-1.0*front->affexpr->children[i]->children[0]->expression[0])

stringstream buffer;

struct cond{
	bool strict;
	vector<string> c;
	string negative_d; //negative component of d
	cond(int equation_count,int toChange,node* change,int src,int dest1,int dest2 = -1,double probability = -1.0){
		strict = false;
		c.resize(nVariables);
		if(dest2==-1){
			if(change==NULL){
				buffer.clear();
				buffer.str(string());
				buffer<<"eps"<<equation_count<<"-f_"<<src<<"_0+f_"<<dest1<<"_0";
				negative_d = buffer.str();
				for(int i=0;i<nVariables;i++){
					buffer.clear();
					buffer.str(string());
					buffer<<"f_"<<dest1<<"_"<<i+1<<"-f_"<<src<<"_"<<i+1;
					c[i] = buffer.str();
				}
			}
			else{
				buffer.clear();
				buffer.str(string());
				buffer<<"eps"<<equation_count<<"-f_"<<src<<"_0+f_"<<dest1<<"_0";
				if(change->expression[0]<0.0){
					buffer<<change->expression[0]<<"f_"<<dest1<<"_"<<toChange;
				}
				else if(change->expression[0]>0.0){
					buffer<<"+"<<change->expression[0]<<"f_"<<dest1<<"_"<<toChange;
				}
				negative_d = buffer.str();
				for(int i = 0;i<nVariables;i++){
					buffer.clear();
					buffer.str(string());
					if((i+1)!=toChange){ // x = blabla y
						buffer<<"f_"<<dest1<<"_"<<i+1;
						if(change->expression[i+1]>0.0){
							buffer<<"+"<<change->expression[i+1]<<"f_"<<dest1<<"_"<<toChange;
						}
						else if(change->expression[i+1]<0.0){
							buffer<<change->expression[i+1]<<"f_"<<dest1<<"_"<<toChange;
						}
					}
					else{
						if(change->expression[i+1]!=0.0){
							buffer<<change->expression[i+1]<<"f_"<<dest1<<"_"<<toChange;
						}
					}
					buffer<<"-f_"<<src<<"_"<<i+1;
					c[i] = buffer.str();
				}
			}
		}
		else{
			// It was a stochastic node, means change would have been NULL
			buffer.clear();
			buffer.str(string());
			buffer<<"eps"<<equation_count<<"-f_"<<src<<"_0+"<<probability<<"f_"<<dest1<<"_0+"<<1.0-probability<<"f_"<<dest2<<"_0"; 
			negative_d = buffer.str();
			for(int i=0;i<nVariables;i++){
				buffer.clear();
				buffer.str(string());
				buffer<<probability<<"f_"<<dest1<<"_"<<i+1<<"+"<<1.0-probability<<"f_"<<dest2<<"_"<<i+1<<"-f_"<<src<<"_"<<i+1;
				c[i] = buffer.str();
			}
		}
	}
	cond(int location_id){
		strict = (location_id!=2);
		c.resize(nVariables);
		for(int i=0;i<nVariables;++i){
			buffer.clear();
			buffer.str(string());
			buffer<<"-f_"<<location_id<<"_"<<i+1;
			c[i] = buffer.str();
		}
		buffer.clear();
		buffer.str(string());
		buffer<<"-f_"<<location_id<<"_"<<0;
		negative_d = buffer.str();
	}
};

struct equation{
	node* affexpr;
	cond* condition;
	equation(){
		affexpr = NULL;
		condition = NULL;
	}
	equation(node* affexpr,cond* condition){
		this->affexpr = affexpr;
		this->condition = condition;
	}
};

map<int,equation*> equations;
int equations_counter = 0;
int epsilons_used = 0;
vector<int> unranked_eps;
map<int,vector<int>> eps_map_eqs;
int n_eqs = 1;
/*

	This function fills in the map "equations" with all the equations initially with the relevant conditions and changes

*/
void generate_equations(){
	// Iterate through all the states and their edges to generate the relevant decrement conditions
	for(map<int,CFG_location*>::iterator it = label_map.begin();it!=label_map.end();++it){
		if(it->second->invariant==NULL){
			// The invariant was "false", so just leave all the transitions of this state
			continue;
		}
		// it->second->invariant->print();
		// cout<<endl;
		if(it->second->type=="det"){
			//Invariant and guard imply the value decrease
			if(it->second->edges.empty()){
				//Code for the last node. No condition
			}
			else if(it->second->edges.size()==1){
				//First make a condition
				cond* condition = new cond(++equations_counter,it->second->edges[0].toChange,it->second->edges[0].change,it->first,it->second->edges[0].next->label);
				// Guard would have been true here
				// Invariant implies the given condition
				int nEquations = it->second->invariant->children.size();
				for(int i=0;i<nEquations;i++){
					equations[n_eqs] = new equation(it->second->invariant->children[i],condition);
					n_eqs++;
				}
				unranked_eps.push_back(equations_counter);
			}
			else{
				//First make the 2 conditions required
				cond* condition0 = new cond(++equations_counter,-1,NULL,it->first,it->second->edges[0].next->label);
				unranked_eps.push_back(equations_counter);
				cond* condition1 = new cond(++equations_counter,-1,NULL,it->first,it->second->edges[1].next->label);
				unranked_eps.push_back(equations_counter);
				// Size is 2, so considering the guards is important and guards cannot be NULL
				if(it->second->invariant==NULL or it->second->edges[0].guard==NULL or it->second->edges[1].guard==NULL){
					//This should never be the case as this would pose conditions that c==0 and d>0, which are not good
					cerr<<"No invariant or no guard specified here"<<endl;
				}
				else{
					//First take and of guard and invariant and then make the corresponding equations
					node* n0 = and_node(it->second->invariant,it->second->edges[0].guard);
					node* n1 = and_node(it->second->invariant,it->second->edges[1].guard);
					int nEquations = n0->children.size();
					for(int i=0;i<nEquations;i++){
						equations[n_eqs] = new equation(n0->children[i],condition0);
						n_eqs++;
						// equations.push(new equation(n0->children[i],condition0));
					}
					nEquations = n1->children.size();
					for(int i=0;i<nEquations;i++){
						equations[n_eqs] = new equation(n1->children[i],condition1);
						n_eqs++;
						//equations.push(new equation(n1->children[i],condition1));
					}
				}
			}
		}
		else if(it->second->type=="ndet"){
			// First make the 2 conditions required
			cond* condition0 = new cond(++equations_counter,-1,NULL,it->first,it->second->edges[0].next->label);
			unranked_eps.push_back(equations_counter);
			cond* condition1 = new cond(++equations_counter,-1,NULL,it->first,it->second->edges[1].next->label);
			unranked_eps.push_back(equations_counter);
			//Invariant implies the value decrease for both the emerging transitions
			int nEquations = it->second->invariant->children.size();
			for(int i=0;i<nEquations;i++){
				equations[n_eqs] = new equation(it->second->invariant->children[i],condition0);
				n_eqs++;
				// equations.push(new equation(it->second->invariant->children[i],condition0));
			}
			for(int i=0;i<nEquations;i++){
				equations[n_eqs] = new equation(it->second->invariant->children[i],condition1);
				n_eqs++;
				// equations.push(new equation(it->second->invariant->children[i],condition1));
			}
		}
		else{
			//Make one condition for the expected value decrease
			cond* condition = new cond(++equations_counter,-1,NULL,it->first,it->second->edges[0].next->label,it->second->edges[1].next->label,it->second->edges[0].probability);
			unranked_eps.push_back(equations_counter);
			//Invariant implies the value decrease of expected value of ranking function, "prob" type node
			int nEquations = it->second->invariant->children.size();
			for(int i=0;i<nEquations;i++){
				equations[n_eqs] = new equation(it->second->invariant->children[i],condition);
				n_eqs++;
				// equations.push(new equation(it->second->invariant->children[i],condition));
			}
		}
	}
	epsilons_used = equations_counter;
	// Initialize eps_map_eqs
	for(map<int,equation*>::iterator eit = equations.begin(); eit!=equations.end();++eit){
		int first_e = eit->second->condition->negative_d.find("eps");
		int first_minus = eit->second->condition->negative_d.find_first_of('-');
		int eps_id_len = first_minus - first_e - 3;
		if(first_e == 0){ // start with eps
			int eps_id = stoi(eit->second->condition->negative_d.substr(first_e+3,eps_id_len));
			eps_map_eqs[eps_id].push_back(eit->first);
		}
	}

	for(map<int,CFG_location*>::iterator it = label_map.begin();it!=label_map.end();++it){
		// Invariant implies the ranking function to be positive
		int nEquations = 0;
		if(it->second->invariant!=NULL){
			nEquations = it->second->invariant->children.size();
		}
		for(int i=0;i<nEquations;i++){
			cond* condition = new cond(it->first);
			++equations_counter;
			equations[n_eqs] = new equation(it->second->invariant->children[i],condition);
			n_eqs++;
			// equations.push(new equation(it->second->invariant->children[i],condition));
		}
	}
	n_eqs -= 1;
}

int last_used_lambda = 0;

/*

	Print the equations.lp file, it just prints the constraints which are still there in the map "equations"

*/
void print_equations(ostream& equationsfile){
	last_used_lambda = 0;
	equationsfile<<"maximize ";
	for(vector<int>::iterator vit = unranked_eps.begin(); vit!=unranked_eps.end(); ++vit){
		equationsfile<<"+eps"<<*vit;
	}
	equationsfile<<"\n\nst\n\n";
	for(vector<int>::iterator vit = unranked_eps.begin(); vit!=unranked_eps.end(); ++vit){
		equationsfile<<"eps"<<*vit<<" >= 0\neps"<<*vit<<" <= 1"<<endl;
	}
	

	for(map<int,equation*>::iterator it = equations.begin();it!=equations.end();++it){
		equation* front = it->second;
		// A(i,j) means affexpr->children[i]->children[0]->expression[j+1] and b(i) translates to -1.0*affexpr->children[i-1]->children[0]->expression[0]
		// Creating a macro for this
		//Printing equations
		int size = front->affexpr->children.size();
		for(int i=0;i<nVariables;++i){  // j is the j-th part of the left-hand side of the implication; i is the i-th reward
			// Each iteration, print out a new equation! :)
			equationsfile<<front->condition->c[i];
			for(int j=0;j<size;++j){
				if(A(j,i)>0){
					equationsfile<< -A(j,i)<<"l"<<to_string(last_used_lambda+j);
				}
				else if(A(j,i)<0){
					equationsfile<<"+"<< -A(j,i)<<"l"<<to_string(last_used_lambda+j);
				}
			}
			equationsfile<<" = 0"<<endl;
		}
		// Printing the last equation
		equationsfile<<front->condition->negative_d;
		for(int j=0;j<size;++j){
			if(b(j)>0){
				equationsfile<<"+"<<b(j)<<"l"<<to_string(last_used_lambda+j);
			}
			else if(b(j)<0){
				equationsfile<<b(j)<<"l"<<to_string(last_used_lambda+j);
			}
			// if(front->affexpr->children[j]->strict){
			// 	equationsfile<<'-'<<'g'<<to_string(last_used_lambda+j);
			// }
		}
		if(front->condition->strict){
			equationsfile<<" <= 0"<<endl;
		}
		else{
			equationsfile<<" <= 0"<<endl;
		}
		last_used_lambda += size;
	}

	equationsfile<<"\nbounds\n\n";
	//Loop to print bounds on other variables
	for(map<int,CFG_location*>::iterator it = label_map.begin();it!=label_map.end();++it){
		for(int j=0;j<=nVariables;j++){
			equationsfile<<"-inf<= f_"<<it->first<<"_"<<j<<" <= +inf"<<endl;
		}
	}
	equationsfile<<"end"<<endl;
}

/*

	Process the files/EquationsOutput file and remove the equations for which epsilons are 0
	Also return the state relevant to determine the further step in the algorithm

*/
int dimension_used = 0;
bool process_equations_output(){
	vector<double> temp(nVariables+1,0);
	for(map<int,CFG_location*>::iterator it = label_map.begin();it!=label_map.end();++it){
		it->second->lexrsm.push_back(temp);
	}
	bool to_return = false;
	ifstream to_process("files/EquationsOutput");
	string line;
	getline(to_process,line);
	if(line=="CPLEX> Variable Name           Solution Value"){
		string temp1,temp2;
		while(to_process>>temp1>>temp2){
			if(temp1.length()>3){
				if(temp1.substr(0,3)=="eps"){
					int eps_id = stoi(temp1.substr(3));
					for(vector<int>::iterator vit = eps_map_eqs[eps_id].begin(); vit!=eps_map_eqs[eps_id].end();vit++){
						equations.erase(*vit);
					}
					for(vector<int>::iterator uit = unranked_eps.begin();uit!=unranked_eps.end();uit++){
						if(*uit==eps_id){
							unranked_eps.erase(uit);
							break;
						}
					}
					to_return = true;
					//Removing those equations whose epsilon is 1
				}
				else if(temp1.substr(0,2)=="f_"){
					int underscore = -1;
					for(int i = 2;i<temp1.length();++i){
						if(temp1[i]=='_'){
							underscore = i;
							break;
						}
					}
					label_map[stoi(part(temp1,2,underscore))]->lexrsm[dimension_used][stoi(part(temp1,underscore+1,temp1.length()))] = stod(temp2);
				}
			}
		}
	}
	dimension_used++;
	return to_return;
}

/*

	Generates start invariant, if there, before invariant generation for putting it into the start condition or the init region in the fast file

*/
string start_invariant(){
	if(label_map[1]->invariant == NULL){
		return "true";
	}
	else{
		buffer.clear();
		buffer.str(string());
		label_map[1]->invariant->print(buffer,"&&","||");
		return buffer.str();
	}
}

int last_dummy_state_used = 0; // Similar to last_label_used, only it is for dummy states rather than the regular ones

/*

	Prints the CFG_generated by parsing into fast format, the format supported by aspic
	This also takes care of the probabilistic assignments, and generates the fast file, as if the transitions to and from dummy states were present

*/
void print_fast(ostream& fastfile){
	fastfile<<"model main{\n\n";
	fastfile<<"\tvar "<<variable[1];
	for(int i=2;i<=nVariables;++i){
		fastfile<<", "<<variable[i];
	}
	fastfile<<";\n\n";

	fastfile<<"\tstates state_1";
	for(int i=2;i<=last_used_label;++i){
		fastfile<<", state_"<<i;
	}
	// The dummy states are for the probabilistic assignments are not in the pCFG.
	for(int i=1;i<=dummy_states_needed;++i){
		fastfile<<",dummy_"<<i;
	}
	fastfile<<";\n\n";

	for(int i=1;i<=last_used_label;++i){
		CFG_location* state = label_map[i];
		for(int j=0;j<state->edges.size();++j){
			if(state->edges[j].change!=NULL){
				if(state->edges[j].change->delta!=0){
					// If delta is not zero, this means that the assignment was a probabilistic one, so use two new dummy states and write the four transitions into the fast file
					//diverge 1
					++last_dummy_state_used;
					fastfile<<"\ttransition t_"<<i<<"_"<<j<<"_diverge1"<<" := {\n";
					fastfile<<"\t\tfrom\t:= state_"<<i<<";\n";
					fastfile<<"\t\tto\t:= dummy_"<<last_dummy_state_used<<";\n";
					if(state->edges[j].guard!=NULL){
						cerr<<"guard in an assignment"<<endl;
					}
					fastfile<<"\t\tguard\t:= true;\n";
					fastfile<<"\t\taction\t:= ;\n\t};\n\n";
					//converge 1
					fastfile<<"\ttransition t_"<<i<<"_"<<j<<"_converge1"<<" := {\n";
					fastfile<<"\t\tfrom\t:= dummy_"<<last_dummy_state_used<<";\n";
					fastfile<<"\t\tto\t:= state_"<<state->edges[j].next->label<<";\n";
					if(state->edges[j].guard!=NULL){
						cerr<<"guard in an assignment"<<endl;
					}
					fastfile<<"\t\tguard\t:= true;\n";
					fastfile<<"\t\taction\t:= ";
					if(state->edges[j].change!=NULL){
						fastfile<<variable[state->edges[j].toChange]<<"' = ";
						state->edges[j].change->print(fastfile,"&&","||","",true);
						fastfile<<"+"<<state->edges[j].change->delta;
					}
					fastfile<<";\n\t};\n\n";
					

					//diverge 2
					++last_dummy_state_used;
					fastfile<<"\ttransition t_"<<i<<"_"<<j<<"_diverge2"<<" := {\n";
					fastfile<<"\t\tfrom\t:= state_"<<i<<";\n";
					fastfile<<"\t\tto\t:= dummy_"<<last_dummy_state_used<<";\n";
					if(state->edges[j].guard!=NULL){
						cerr<<"guard in an assignment"<<endl;
					}
					fastfile<<"\t\tguard\t:= true;\n";
					fastfile<<"\t\taction\t:= ;\n\t};\n\n";
					//converge 2
					fastfile<<"\ttransition t_"<<i<<"_"<<j<<"_converge2"<<" := {\n";
					fastfile<<"\t\tfrom\t:= dummy_"<<last_dummy_state_used<<";\n";
					fastfile<<"\t\tto\t:= state_"<<state->edges[j].next->label<<";\n";
					if(state->edges[j].guard!=NULL){
						cerr<<"guard in an assignment"<<endl;
					}
					fastfile<<"\t\tguard\t:= true;\n";
					fastfile<<"\t\taction\t:= ";
					if(state->edges[j].change!=NULL){
						fastfile<<variable[state->edges[j].toChange]<<"' = ";
						state->edges[j].change->print(fastfile,"&&","||","",true);
						fastfile<<"-"<<state->edges[j].change->delta;
					}
					fastfile<<";\n\t};\n\n";
				}
				else{
					fastfile<<"\ttransition t_"<<i<<"_"<<j<<" := {\n";
					fastfile<<"\t\tfrom\t:= state_"<<i<<";\n";
					fastfile<<"\t\tto\t:= state_"<<state->edges[j].next->label<<";\n";
					fastfile<<"\t\tguard\t:= ";
					if(state->edges[j].guard==NULL){
						fastfile<<"true";
					}
					else{
						node* temp;
						if(label_map[i]->invariant!=NULL){
							temp = and_node(state->edges[j].guard,label_map[i]->invariant);
						}
						else{
							temp = state->edges[j].guard;
						}
						temp->print(fastfile,"&&","||","",true);
					}
					fastfile<<";\n";
					fastfile<<"\t\taction\t:= ";
					if(state->edges[j].change!=NULL){
						fastfile<<variable[state->edges[j].toChange]<<"' = ";
						state->edges[j].change->print(fastfile,"&&","||","",true);
					}
					fastfile<<";\n\t};\n\n";
				}
			}
			else{
				fastfile<<"\ttransition t_"<<i<<"_"<<j<<" := {\n";
				fastfile<<"\t\tfrom\t:= state_"<<i<<";\n";
				fastfile<<"\t\tto\t:= state_"<<state->edges[j].next->label<<";\n";
				fastfile<<"\t\tguard\t:= ";
				if(state->edges[j].guard==NULL){
					fastfile<<"true";
				}
				else{
					node* temp;
					if(label_map[i]->invariant!=NULL){
						temp = and_node(state->edges[j].guard,label_map[i]->invariant);
					}
					else{
						temp = state->edges[j].guard;
					}
					temp->print(fastfile,"&&","||","",true);
				}
				fastfile<<";\n";
				fastfile<<"\t\taction\t:= ;\n\t};\n\n";
			}
		}
	}

	fastfile<<"}\n\nstrategy main_s{\n\n";
	fastfile<<"\tRegion init := {state = state_1 && "<<start_invariant()<<"};\n\n";
	fastfile<<"}";
}

bool checkCommunityBug(){
	ifstream to_process("files/EquationsOutputRaw");
	string targetString = "Problem size limits exceeded";
	bool sizeBug=false;
	string line;
	while(getline(to_process,line)){
		if (line.find(targetString) != std::string::npos) {
            sizeBug = true;
            break;
        }
	}
	return sizeBug;
}

int main(){
	struct timeval  tv1, tv2;
	gettimeofday(&tv1, NULL);
	int start,end;
	char* input = new char[MAXL];
	int r,i;
	// Use File Input
	// FILE *f;
	// f = fopen("./examples/ForExperiments/speedFails2.prob","r");

	// for(i=0;(r=getc(f))!=EOF;i++){
	// 	if(i>MAXL){
	// 		cerr<<"Program longer than the maximum allowed limit of "<<MAXL<<endl;
	// 		exit(0);
	// 	}
	// 	input[i]=r;
	// }
	// Taking program input
	for(i=0;(r=getchar())!=EOF;i++){
		if(i>MAXL){
			cerr<<"Program longer than the maximum allowed limit of "<<MAXL<<endl;
			exit(0);
		}
		input[i]=r;
	}
	// program is the string used for generating the pCFG and stores the program as a whole
	input[i]=0;
	program=input;
	delete[] input;
	int begin = 0;
	int endprog = program.length();	
	skip_spaces(begin,endprog);
	nVariables = find_variables(begin,endprog); //To find the number of different variables of the type x_i in the program
	// Adding the start and end CFG_locations, as they have to be passed into the recursive node constructor
	
	start = ++last_used_label;
	end = ++last_used_label;
	label_map[start] = new CFG_location("det",start);
	label_map[end]	 = new CFG_location("det",end);
	// Parsing program from begin to endprog(pointers) and the start and end nodesid's have also been passed
	root=new node("stmt",begin,endprog,start,end);
	gettimeofday(&tv2, NULL);
	cout<<"Time:"<<(double) (tv2.tv_usec - tv1.tv_usec) / 1000000 +(double) (tv2.tv_sec - tv1.tv_sec)<<endl;
	cout<<"Parsing over and CFG constructed"<<endl;
	cout<<"The CFG constructed has "<<last_used_label<<" states"<<endl;
	ofstream fastfile;
	fastfile.open("files/aspic.fast");
	ostream* outfast = &fastfile;
	// Printing the CFG in fast format into files/aspic.fast file
	print_fast(*outfast);
	fastfile.close();
	gettimeofday(&tv2, NULL);
	cout<<"Time:"<<(double) (tv2.tv_usec - tv1.tv_usec) / 1000000 +(double) (tv2.tv_sec - tv1.tv_sec)<<endl;
	cout<<"Fast file printed."<<endl;
	double aspic_start_time = (double) (tv2.tv_usec - tv1.tv_usec) / 1000000 +(double) (tv2.tv_sec - tv1.tv_sec);
	// Calling the invariant_script.sh which inturn calls aspic to generate invariants into files/InvariantOutput	
	if(system("./files/invariant_script.sh")!=0){
		cerr<<"Something wrong with the script to find invariants";
	}
	gettimeofday(&tv2, NULL);
	cout<<"Time:"<<(double) (tv2.tv_usec - tv1.tv_usec) / 1000000 +(double) (tv2.tv_sec - tv1.tv_sec)<<endl;
	double aspic_end_time = (double) (tv2.tv_usec - tv1.tv_usec) / 1000000 +(double) (tv2.tv_sec - tv1.tv_sec);
	cout<<"Invariants generated using aspic"<<endl;
	// Code for analysing files/InvariantOutput comes here
	ifstream invariant_file("files/InvariantOutput");
	for(int i=1;i<=last_used_label;){
		string line;
		getline(invariant_file,line);
		skip_spaces(line);
		size_t open = line.find('{');
		if(open!=string::npos){
			int first_space = -1;
			for(int i=0;i<line.length();++i){
				if(isspace(line[i])){
					first_space = i;
					break;
				}
			}
			if(first_space==-1){
				cerr<<"Error! No space in the Invariant output concerned line"<<endl;
			}
			if(part(line,0,6)!="state_"){
				continue;
			}
			size_t close = line.find('}');
			string invariant_string = part(line,open+1,close);
			// If the invariant generated is true, interpret it as "0<=0" and add that manually
			// This helps because now we can apply Farkas lemma straight away
			if(invariant_string=="true"){
				if(label_map[stoi(part(line,6,first_space))]->invariant==NULL){
					label_map[stoi(part(line,6,first_space))]->invariant = new node("bexpr");
					node* concerned_node = label_map[stoi(part(line,6,first_space))]->invariant;
					concerned_node->children.resize(1);
					concerned_node->children[0] = new node("affexpr");
					concerned_node->children[0]->children.resize(1);
					concerned_node->children[0]->children[0] = new node("literal");
					concerned_node->children[0]->children[0]->constant = "<=";
					concerned_node->children[0]->children[0]->children.resize(1);
					concerned_node->children[0]->children[0]->children[0] = new node("expr");
					concerned_node->children[0]->children[0]->children[0]->expression.resize(nVariables+1);
				}
			}
			else if(invariant_string!="false"){
				bool temp;
				node* generated_invariant = new node("bexpr",invariant_string,temp);
				if(label_map[stoi(part(line,6,first_space))]->invariant==NULL){
					label_map[stoi(part(line,6,first_space))]->invariant = generated_invariant;
				}
				else if(stoi(part(line,6,first_space))!=1){
					// <flag> This still doesn't look very nice to me
					// The invariant at the start node, is left untouched, all others are conjuncted with the generated invariant
					label_map[stoi(part(line,6,first_space))]->invariant = and_node(label_map[i]->invariant,generated_invariant);
				}
			}
			i++;
		}
	}

	// // Code to print the tree structure etc.
	// // This is needed for debugging
	// cout<<"Input Code:"<<endl;
	// cout<<program<<endl;
	// cout<<"Parse Tree:"<<endl;
	// root->print(cout,"&&","||","*",false);
	// cout<<"CFG:"<<endl;
	// for(map<int,CFG_location*>::iterator it = label_map.begin();it!=label_map.end();++it){
	// 	cout<<"------------------------"<<endl;
	// 	cout<<"Node "<<it->first<<endl;
	// 	it->second->print();
	// 	// cout<<it->second->label<<endl;
	// }

	// Generate equations and store them in the universal map equations, each equation encodes a transition or the non-negativity constraint
	// Each equation can correspond to many constraints when inputted into cplex
	generate_equations();
	ofstream equationsfile;
	bool solved = false;
	gettimeofday(&tv2, NULL);
	cout<<"Time:"<<(double) (tv2.tv_usec - tv1.tv_usec) / 1000000 +(double) (tv2.tv_sec - tv1.tv_sec)<<endl;
	cout<<"Invariants read and equations generated."<<endl;
	int loop_counter=0;
	// The main algorithm implementation
	for(;loop_counter<100;++loop_counter){	
		// An iteration of loop means onw iteration of algorithm
		equationsfile.open("files/equations.lp");
		ostream* equation_output_file = &equationsfile;
		print_equations(*equation_output_file);
		equationsfile.close();
		// Run files/script.sh which calls cplex on file/equations.lp and generates output into  files/EquationsOutput
		// files/EquationsOutput is also trimmed by the script for easy analysis in further steps
		if(system("./files/script.sh")!=0){
			cout<<"Something wrong with the script analysing equations"<<endl;
		}
		//Processing the files/EquationsOutput file function
		bool sizeBug = checkCommunityBug();
		if(sizeBug){
			cout << "The problem is too large for CPLEX community edition!" << endl;
			return 0;
		}
		bool state = process_equations_output();
		string command;
        command = "mv files/EquationsOutput files/EquationsOutput" + to_string(loop_counter);
		system(command.c_str());
		command = "mv files/equations.lp files/equations.lp" + to_string(loop_counter);
		system(command.c_str());
		if(state==false){
			// If all the epsilons were 0, this means that no solution can ever be found by our algorithm
			//string command;
			// command = "mv files/EquationsOutput files/EquationsOutput" + to_string(loop_counter);
			command = "rm files/EquationsOutput files/InvariantOutput files/aspic.fast files/equations.lp";
			// system(command.c_str());
			break;
		}
		else{
			//Some equation was deleted, some epsilon was 1, so enter into another iteration or solution has been found
			if(unranked_eps.size()==0){
				// If the equations due to the epsilons are all removed, this means that we found a solution and hence break from the loop	
				solved = true;
				//string command;
				// command = "mv files/EquationsOutput files/EquationsOutput" + to_string(loop_counter);
				command = "rm files/EquationsOutput files/InvariantOutput files/aspic.fast files/equations.lp";
				// system(command.c_str());
				break;
			}
			else{
				//Move into another iteration
			}
		}
		//string command;
		//Renaming the files/EquationsOutput because it contains the solution
		command = "rm files/EquationsOutput files/InvariantOutput files/aspic.fast files/equations.lp";
		// command = "mv files/EquationsOutput files/EquationsOutput" + to_string(loop_counter);
		// system(command.c_str());
	}

	gettimeofday(&tv2, NULL);
	cout<<"Time:"<<(double) (tv2.tv_usec - tv1.tv_usec) / 1000000 +(double) (tv2.tv_sec - tv1.tv_sec)<<endl;
	// cout<<"Final result: "<<endl;
	// cout<<"=============="<<endl;

	if(solved){
		cout<<"Found a solution of dimension "<<loop_counter+1<<"."<<endl;
		// cout<<"CFG details are:"<<endl;
		// for(map<int,CFG_location*>::iterator it = label_map.begin();it!=label_map.end();++it){
		// 	cout<<"------------------------"<<endl;
		// 	cout<<"|||Node "<<it->first<<"|||"<<endl<<endl;
		// 	it->second->print();
		// 	// cout<<it->second->label<<endl;
		// }
	}
	else{
		cout<<"No solution found, stopped after "<<loop_counter+1<<" iterations"<<endl;
	}
	cout<<"Total time taken: "<<(double) (tv2.tv_usec - tv1.tv_usec) / 1000000 +(double) (tv2.tv_sec - tv1.tv_sec)<<endl;
	cout<<"Time taken by aspic: "<<aspic_end_time-aspic_start_time<<endl;

	// Param Table Collection
	// cout << "Number of variables: " << nVariables << endl;

	// Please use the following codes to output information for largeifs
	// cout << "Number of locations: " << last_used_label << endl;
	// cout << "Invariant time: "<<aspic_end_time-aspic_start_time<<endl;
	// cout << "Our time: " << (double) (tv2.tv_usec - tv1.tv_usec) / 1000000 +(double) (tv2.tv_sec - tv1.tv_sec) - aspic_end_time + aspic_start_time<<endl;
	// cout << "Total time: " << (double) (tv2.tv_usec - tv1.tv_usec) / 1000000 +(double) (tv2.tv_sec - tv1.tv_sec)<<endl;
	return 0;
}