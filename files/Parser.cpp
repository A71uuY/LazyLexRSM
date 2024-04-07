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
#include <stdlib.h>
#include "Parser.h"
using namespace std;
#define MAXL 100000 //Maximum length of the program
#define part(x,a,b) (x.substr((a),((b)-(a))))
#define pb push_back

//variable declarations
string program;
int nVariables;
int last_used_label = 0;
map<int,CFG_location*> label_map;
map<string,int> variableId;
map<int,string> variable;
int dummy_states_needed = 0; // The states needed for the if * transformation of non deterministic assignments
node* root;

/*

	begin and end are the pointers to the concerned string in program
	So, for parsing purposes, skip_spaces changes the pointers accordingly so that the extra spaces at the start and end are out of consideration

*/
void skip_spaces(int &begin, int &end){ //skips the spaces in the beginning and the end
	while(begin<program.size() and isspace(program[begin])){
		begin++;
	}
	while(end>0 and isspace(program[end-1])){
		end--;
	}
}

/*

	line is the concerned string and may contain extra spaces at the begin and end, skip_spaces deletes the extra spaces from start and end of line

*/
void skip_spaces(string& line){
	int begin = 0,end = line.length();
	while(begin<line.size() and isspace(line[begin])){
		begin++;
	}
	while(end>0 and isspace(line[end-1])){
		end--;
	}
	line = part(line,begin,end);
}


/*

	Constructor when only the type of node is specified

*/
node::node(string t){
	bracket = NULL;
	begin = -1;
	end = -1;
	type = t;
	constant = "";
	strict = false;
	delta = 0.0;
	l_bounded = false;
	r_bounded = false;
	not_uni = false;
}

/*

	A general constructor when the
		b: start pointer of the program
		e: end pointer of the program
		s: the id of start node in pCFG
		l: rhe id of final node in pCFG
		negate: a special bool passed for nodes of type "expr" when the expression was of the form -(string1) and now the concerned string becomes string1 and negate becomes 1

*/
node::node(string t, int b, int e, int s, int l, bool negate){
	bracket = NULL;
	type = t;
	begin = b;
	strict = false;
	end = e;
	delta = 0.0;
	l_bounded = false;
	r_bounded = false;
	not_uni = false;
	skip_spaces(begin,end);
	if(begin>end){
		cerr<<"Error! begin= "<<b<<" end= "<<e<<endl;
	}
	process(s,l,negate);
}

/*

	For processing the results of Invariant output a more time and memory expensive function made
	Rather than dealing with pointers in string just passes the string concerned
	t: type of node
	l: string concerned
	to_return: a special boolean introduced because sometimes the string to be parsed can be of the form <expr1>=<expr2>
		In such cases, we interpret it as <expr1> <= <expr2> and control the return_bool so that code then adds <expr1> >= <expr2> after this function is called
		The other literal has to be forcefully added depending upon the return value

*/
node::node(string t, string l, bool& to_return){
	strict = false;
	type = t;
	delta = 0.0;
	l_bounded = false;
	r_bounded = false;
	not_uni = false;
	if(t=="bexpr"){
		stringstream line_stream;
		line_stream.str(l);
		string semicolon_sep;
		while(getline(line_stream,semicolon_sep,';')){	
			node* affexpr_temp = new node("affexpr");
			stringstream line_stream1;
			line_stream1.str(semicolon_sep);
			string comma_sep;
			while(getline(line_stream1,comma_sep,',')){
				skip_spaces(comma_sep);
				bool return_value = false;
				node* formed_literal = new node("literal",comma_sep, return_value);
				affexpr_temp->children.pb(formed_literal);
				if(return_value){
					node* other_literal = new node("literal");
					other_literal->constant = "<=";
					other_literal->children.resize(1);
					other_literal->children[0] = new node("expr");
					other_literal->children[0]->expression.resize(nVariables+1);
					for(int i=0;i<=nVariables;++i){
						other_literal->children[0]->expression[i] = -1.0*formed_literal->children[0]->expression[i];
					}
					affexpr_temp->children.pb(other_literal);

				}
			}
			children.pb(affexpr_temp);
		}
	}
	else if(t=="literal"){
		constant = "and";
		if(proc_literal(false,false,l)){
			to_return = true;
		}
	}
	else if(t=="expr"){
		constant = "expression";
		proc_expr(l);
	}
	else{
		cerr<<"Wrong usage"<<endl;
		return;
	}
	
}

/*

	copies the node* vector from tocopy to sink, was needed for operations with negate and and_node
	Operations on bexpr needed this

*/
void vcopy(vector<node*> &sink,vector<node*> &tocopy){
	sink.clear();
	int size = tocopy.size();
	sink.resize(size);
	for(int i=0;i<size;++i){
		sink[i] = new node(tocopy[i]->type);
		sink[i]->constant = tocopy[i]->constant;
		sink[i]->begin = tocopy[i]->begin;
		sink[i]->end = tocopy[i]->end;
		sink[i]->bracket = tocopy[i]->bracket;
		sink[i]->expression = tocopy[i]->expression;
		sink[i]->children = tocopy[i]->children;
	}
}

/*

	returns a bexpr node which is negative of the tonegate bexpr node
	Was necessary because both have to be in DNF, disjunctive normal form

*/
node* negation(node* tonegate){
	if(tonegate->type=="bexpr" and tonegate->constant=="or"){
		vector<node*> before_multiplication;
		node* negative;
		negative = new node("bexpr");
		negative->constant = "or";
		negative->children.resize(1);
		negative->children[0] = new node("affexpr");
		negative->children[0]->constant = "and";
		int ORs = tonegate->children.size();
		for(int i = 0;i<ORs;++i){
			//Multply this set of AND to the present collection
			vcopy(before_multiplication,negative->children);
			vector<node*> after_multiplication;
			int before_size = before_multiplication.size();
			negative->children.clear();
			int ANDs = tonegate->children[i]->children.size();
			for(int j = 0;j<ANDs;++j){
				node* ch = new node("literal");
				ch->constant = "<=";
				ch->children.resize(1);
				ch->children[0] = new node("expr");
				ch->children[0]->constant = "expression";
				ch->children[0]->expression.resize(nVariables+1);
				ch->strict = !(tonegate->children[i]->children[j]->strict);
				for(int k=0;k<=nVariables;++k){
					ch->children[0]->expression[k] = -1.0*tonegate->children[i]->children[j]->children[0]->expression[k];
				}
				vcopy(after_multiplication,before_multiplication);
				for(int k = 0;k<before_size;++k){
					after_multiplication[k]->children.pb(ch);
				}
				negative->children.insert(negative->children.end(),after_multiplication.begin(),after_multiplication.end());
				//Appending the children after appending one element from the to be multiplied set to each of the children
			}
		}
		return negative;
	}
	cerr<<"Wrong argument in negation, passed a"<<tonegate->type<<endl;	
	return NULL;
}

/*

	Returns a bexpr node which is the and of the bexpr nodes "one" and "two".
	Necessary because both have to be in DNF, disjunctive normal form in terms of literals

*/
node* and_node(node* one,node* two){
	if(one->type!="bexpr" or two->type!="bexpr"){
		cerr<<"Taking and of wrong type of nodes"<<endl;
		return NULL;
	}
	node* node_and = NULL;
	node* temp_affexpr = NULL;
	node_and = new node("bexpr");
	node_and->constant = "or";
	int a = one->children.size(), b = two->children.size();
	for(int i = 0;i<a;i++){
		for(int j = 0;j<b;j++){
			temp_affexpr = new node("affexpr");
			temp_affexpr->constant = "and";
			temp_affexpr->children = one->children[i]->children;
			temp_affexpr->children.insert(temp_affexpr->children.end(),two->children[j]->children.begin(),two->children[j]->children.end());
			node_and->children.pb(temp_affexpr);
		}
	}
	return node_and;
}

/*

	processes this node, given it is of type statement
	s: initial node id in pCFG
	l: destination node id in pCFG

*/
void node::proc_stmt(int s,int l){
	
	// Code to add invariants manually at each node
	skip_spaces(begin,end);
	if(program[begin]=='['){
		int closed_bracket = -1;
		for(int j = begin+1;j<end;++j){
			if(program[j]==']'){
				closed_bracket = j;
				break;
			}
		}
		bracket = new node("bexpr",begin+1,closed_bracket);
		label_map[s]->invariant = bracket;
		begin = closed_bracket+1;
	}
	
	skip_spaces(begin,end);
	if(part(program,begin,end)=="skip"){
		constant = "skip";
		CFG_edge temporary_edge(label_map[l],-1,NULL);
		label_map[s]->edges.pb(temporary_edge);
		return;
	}
	//look for semicolons
	int open = 0; //open if's and while's
	for(int i = begin;i<end;++i){
		if(part(program,i,i+2)=="if" or part(program,i,i+5)=="while" or program[i]=='('){ //Can give seg faults in some extremely unlucky situations
			open++;
		}
		else if(part(program,i,i+2)=="od" or part(program,i,i+2)=="fi" or program[i]==')'){ //Can give errors in stupid cases
			open--;
		}
		else if(open==0 and program[i]==';'){
			constant = "several statements";
			children.resize(2);
			int mid = ++last_used_label;
			label_map[mid] = new CFG_location("det",mid);
			children[0] = new node("stmt",begin,i,s,mid);
			children[1] = new node("stmt",i+1,end,mid,l);
			return;
		}
	}

	//look for brackets
	// Assuming the invariants are at the beginning itself
	skip_spaces(begin,end);
	

	//check if it is a while
	if(part(program,begin,begin+5)=="while"){
		int firstdo = -1,lastod = -1;
		for(int i = begin;i<end;++i){
			if(part(program,i,i+2)=="do"){
				firstdo = i;
				break;
			}
		}
		for(int i = end-2;i>=begin;--i){
			if(part(program,i,i+2)=="od"){
				lastod = i;
				break;
			}
		}
		if(firstdo==-1 or lastod==-1){
			cerr<<"Bad while in range ["<<begin<<","<<end<<")"<<endl;
		}
		constant = "while";
		children.resize(2);
		children[0] = new node("bexpr",begin+5,firstdo);
		int mid = ++last_used_label;
		int s_dup = ++last_used_label;
		label_map[mid] = new CFG_location("det",mid);
		label_map[s_dup] = new CFG_location("det",s_dup);
		node* temporary_node;
		temporary_node = negation(children[0]);
		CFG_edge temporary_edge1(label_map[mid],-1,NULL,children[0]);
		CFG_edge temporary_edge2(label_map[l],-1,NULL,temporary_node);
		label_map[s]->edges.pb(temporary_edge1);
		label_map[s_dup]->edges.pb(temporary_edge1);
		label_map[s]->edges.pb(temporary_edge2);
		label_map[s_dup]->edges.pb(temporary_edge2);
		children[1] = new node("stmt",firstdo+2,lastod,mid,s_dup);
		return;
	}
	//check if it is an if
	if(part(program,begin,begin+2)=="if"){
		int firstthen = -1; //first then
		for(int i = begin;i<end;++i){
			if(part(program,i,i+4)=="then"){
				firstthen = i;
				break;
			}
		}
		int lastfi = -1;
		for(int i = end-1;i>=begin;--i){
			if(part(program,i,i+2)=="fi"){
				lastfi = i;
				break;
			}
		}
		if(lastfi==-1 or firstthen==-1){
			cerr<<"Invalid if between ["<<begin<<", "<<end<<")"<<endl;
		}
		int correselse = -1; //corresponding else
		int ifcnt = 0;
		for(int i = begin;i<end;++i){
			if(part(program,i,i+2)=="if"){
				ifcnt++;
			}
			else if(part(program,i,i+4)=="else"){
				ifcnt--;
				if(ifcnt==0){
					correselse = i;
					break;
				}
			}
		}
		int case1 = ++last_used_label;
		int case2 = ++last_used_label;
		label_map[case1] = new CFG_location("det",case1);
		label_map[case2] = new CFG_location("det",case2);
		CFG_edge temporary_edge1(label_map[case1],-1,NULL);
		CFG_edge temporary_edge2(label_map[case2],-1,NULL);
		constant = "if";
		children.resize(3);
		children[0] = new node("ndbexpr",begin+2,firstthen);
		if(children[0]->constant=="prob"){
			label_map[s]->type = "prob";
			temporary_edge1.probability = stod(children[0]->children[0]->constant);
			label_map[s]->edges.pb(temporary_edge1);
			temporary_edge2.probability = 1.0 - temporary_edge1.probability;
			label_map[s]->edges.pb(temporary_edge2);
		}
		else if(children[0]->constant=="star"){
			label_map[s]->type = "ndet";
			label_map[s]->edges.pb(temporary_edge1);
			label_map[s]->edges.pb(temporary_edge2);
		}
		else{
			temporary_edge1.guard = children[0]->children[0]; //It is ndbexpr->bexpr
			temporary_edge2.guard = negation(children[0]->children[0]);
			label_map[s]->edges.pb(temporary_edge1);
			label_map[s]->edges.pb(temporary_edge2);
		}
		children[1]=new node("stmt",firstthen+4,correselse,case1,l);
		children[2]=new node("stmt",correselse+4,lastfi,case2,l);
		return;
	}

	//The statement is a assignment
	constant = "single assgn";
	children.resize(1);
	children[0] = new node("assgn",begin,end,s,l);
}

/*

	processes this node, given it is of type assignment
	s: initial node id in pCFG
	l: destination node id in pCFG
	
*/
void node::proc_assgn(int s,int l){
	skip_spaces(begin,end);
	int pos = -1;
	for(int i = begin;i<end;++i){
		if(part(program,i,i+2)==":="){
			pos = i;
			break;
		}
	}
	if(pos==-1){
		cerr<<"Wrong assignment between ["<<begin<<","<<end<<") i.e. "<<part(program,begin,end)<<endl;
	}
	else{
		children.resize(2);
		children[0] = new node("pvar",begin,pos);
		//Checking the sample() format
		int samplepos = pos+2;
		while(isspace(program[samplepos])){
			samplepos++;
		}
		constant = "simple assignment";
		children[1] = new node("expr",pos+2,end); //rexpr is nothing but an expr, a expression
		label_map[s]->type = "det";
		CFG_edge temporary_edge(label_map[l],variableId[part(program,children[0]->begin,children[0]->end)],children[1]);
		label_map[s]->edges.pb(temporary_edge);
	}
}

/*

	processes this node, given it is of type affine expression
		
*/
void node::proc_affexpr(){
	constant = "and";
	skip_spaces(begin,end);
	int AND = -1;
	for(int i = begin+1;i<end-3;++i){
		if(part(program,i,i+3)=="and" and isspace(program[i-1]) and isspace(program[i+3])){
			AND = i;
			break;
		}
	}
	if(AND==-1){
		node* ch = new node("literal",begin,end);
		children.pb(ch);
	}
	else{
		node* ch = new node("literal",begin,AND);
		int begin_backup = begin;
		children.pb(ch);
		begin = AND + 3;
		proc_affexpr();
		begin = begin_backup;
	}
}

/*

	processes this node, given it is of type single variable
		
*/
void node::proc_pvar(){
	skip_spaces(begin,end);
	constant = part(program,begin,end);
}

void node::analyse_expr(int begin,int end,bool negate){
	skip_spaces(begin,end);
	if(program[begin]=='['){
		if(program[end-1]==']'){
			int comma = -1;
			int comma_2nd = -1;
			for(int i=begin;i<end;i++){
				if(program[i]==','){
					if(comma == -1){
						comma = i;
					}
					else{  // There is another comma, read as not_uni support
						comma_2nd = i;
					}
				}
			}
			if(comma==-1){
				cerr<<"No comma in [a,b] literal between "<<begin<<","<<end<<endl;
			}
			else{
				if(comma_2nd != -1){ // not_uni distribution, two commas
					not_uni = true;
					string mean_value = part(program,begin+1,comma);
					string lower = part(program,comma+1,comma_2nd);
					string upper = part(program,comma_2nd+1,end-1);
					skip_spaces(lower);
					skip_spaces(upper);
					if(lower == "infty" || upper == "-infty"){
						cerr<<"Invalid distribution"<<endl;
					}
					if(lower != "-infty"){
						l_bounded = true;
					}
					if(upper != "infty"){
						r_bounded = true;
					}
					double mean_val = stod(mean_value);
					if(l_bounded){
						lb = stod(lower);
					}
					if(r_bounded){
						ub = stod(upper);
					}
					if(negate){
						expression[0] -= mean_val;
					}
					else{
						expression[0] += mean_val;
					}
					delta += -10; // just a foobar value to indicate 'this is a prob branch'
				}
				else{  // Uniform distribution, one comma
					string lower = part(program,begin+1,comma);
					string upper = part(program,comma+1,end-1);
					skip_spaces(lower);
					skip_spaces(upper);
					double lower_bound = stod(lower);
					double upper_bound = stod(upper);
					if(lower_bound<=upper_bound){
						if(negate){
							expression[0] -= (upper_bound+lower_bound)/2.0;
							
						}
						else{
							expression[0] += (upper_bound+lower_bound)/2.0;
						}
						delta += (upper_bound-lower_bound)/2.0;
					}
					else{
						cerr<<"Lower bound is greater than upper bound between "<<begin<<","<<end<<endl;
					}
				}
			}
		}
		else{
			cerr<<"Wrong format for [a,b] literal between "<<begin<<","<<end<<endl;
		}
		return;
	}
	int star = -1;
	for(int i = begin;i<end;++i){ //Assuming that the program variable names don't contain star anywhere
		if(program[i]=='*'){
			star = i;
		}
	}
	if(star==-1){
		if(isdigit(program[begin])){
			if(negate){
				expression[0] -= stod(part(program,begin,end));
			}
			else{
				expression[0] += stod(part(program,begin,end));
			}
		}
		else{
			if(negate){
				expression[variableId[part(program,begin,end)]] -= 1.0;
			}
			else{
				expression[variableId[part(program,begin,end)]] += 1.0;
			}
		}
	}
	else{
		int block=star+1;
		skip_spaces(begin,star);
		skip_spaces(block,end);
		map<string, int>::iterator it = variableId.find(part(program,block,end));
		if(it==variableId.end()){
			cerr<<"Error in the variable in ["<<block<<","<<end<<")"<<"begin = "<<begin<<endl;
		}
		expression[it->second] += stod(part(program,begin,star));
	}
}

void node::analyse_expr(string l,bool negate){
	int x_pos = -1;
	for(int i = 0;i<l.length();++i){
		if(!isdigit(l[i]) and l[i]!='.'){
			x_pos = i;
			break;
		}
	}
	if(x_pos!=-1){
		if(x_pos==0){
			if(negate){
				expression[variableId[part(l,x_pos,l.length())]] -= 1.0;
			}
			else{
				expression[variableId[part(l,x_pos,l.length())]] += 1.0;
			}
		}
		else{
			if(negate){
				expression[0] -= stod(part(l,0,x_pos));
			}
			else{
				expression[0] += stod(part(l,0,x_pos));
			}
		}
	}
	else{
		if(negate){
			expression[0] -= stod(l);
		}
		else{
			expression[0] += stod(l);
		}
	}
}

void node::form_vector(int begin,int end,bool negate){ //Note that this shadows the original ones
	skip_spaces(begin,end);
	int plusminus = -1;
	// Implemented as a linear but still recursive function
	int open_brackets = 0;
	for(int i = begin;i<end;++i){
		if(program[i]=='['){
			open_brackets++;
		}
		else if(program[i]==']'){
			open_brackets--;
		}
		if((program[i]=='+' or program[i]=='-') and open_brackets==0){
			plusminus = i;
			break;
		}
	}
	if(plusminus!=-1){
		if(plusminus==begin){
			form_vector(plusminus+1,end,program[plusminus]=='-' xor negate);
		}
		else{
			analyse_expr(begin,plusminus,negate);
			form_vector(plusminus+1,end,program[plusminus]=='-');
		}
	}
	else{
		analyse_expr(begin,end,negate);
	}
}

void node::form_vector(string l,bool negate){
	skip_spaces(l);
	int plusminus = -1;
	// Implemented as a linear but still recursive function
	int open_brackets = 0;
	for(int i = 0;i<l.length();++i){
		if(l[i]=='['){
			open_brackets++;
		}
		else if(l[i]==']'){
			open_brackets--;
		}
		if((l[i]=='+' or l[i]=='-') and open_brackets==0){
			plusminus = i;
			break;
		}
	}
	if(plusminus!=-1){
		analyse_expr(part(l,0,plusminus),negate);
		form_vector(part(l,plusminus+1,l.length()),l[plusminus]=='-');
	}
	else{
		analyse_expr(l,negate);
	}
}

/*

	processes this node, given it is of type expression
		
*/
void node::proc_expr(){
	skip_spaces(begin,end);
	constant = "expression";
	expression.resize(nVariables+1);
	form_vector(begin,end,false);
	if (delta!=0){
		dummy_states_needed += 2;
	}
}

/*

	processes this node, given it is of type expression
	For parsing the Invariant Output
	l: The string which is to be parsed
	
*/
void node::proc_expr(string l){
	skip_spaces(l);
	expression.resize(nVariables+1);
	form_vector(l,false);
}

/*

	processes this node, given it is of type constant
		
*/
void node::proc_constant(){
	skip_spaces(begin,end);
	constant = part(program,begin,end);
	if(constant[0]=='.'){
		constant="0"+constant;
	}
}

/*

	processes this node, given it is of type literal
	negate: A boolean whether this expression should be handled as a negative of what is in the concerned region
	strategic: If it is false, the concerned string is from program. Otherwise it is the line which is one of the parameters
	
*/
bool node::proc_literal(bool negate,bool strategic, string line){
	bool to_return = false;
	if(strategic){
		skip_spaces(begin,end);
		if(program[begin]=='~' or program[begin]=='!'){ //Assuming the sign for negation could be '!' or '~'
			begin = begin+1;
			proc_literal(!negate);
			return to_return;
		}
		int sign = -1;
		for(int i = begin;i<end-1;++i){
			if(program[i]=='<' or program[i]=='>'){
				sign = i;
				break;
			}
		}
		if(sign==-1){
			cerr<<"Invalid literal between "<<begin<<" "<<end<<endl;
		}
		else{
			if(program[sign+1]=='='){
				if(!negate){
					constant=part(program,sign,sign+2);
				}
				else{
					if(part(program,sign,sign+2)==">="){
						constant = "<=";
					}
					else{
						constant = ">=";
					}
				}
				children.resize(2);
				children[0] = new node("expr",begin,sign);
				children[1] = new node("expr",sign+2,end);
			}
			else{
				strict = true;
				if(!negate){
					if(program[sign]=='>'){
						constant = ">=";
					}
					else{
						constant = "<=";
					}
				}
				else{
					if(program[sign]=='>'){
						constant = "<=";
					}
					else{
						constant = ">=";
					}
				}
				children.resize(2);
				children[0] = new node("expr",begin,sign);
				children[1] = new node("expr",sign+1,end);
			}
		}
	}
	else{
		int sign = -1;
		for(int i=0;i<line.length()-1;++i){
			if(line[i]=='<' or line[i]=='>' or line[i]=='='){
				sign = i;
				break;
			}
		}
		children.resize(2);
		bool temp;
		children[0] = new node("expr",part(line,0,sign),temp);
		if(sign==-1){
			cerr<<"Invalid literal";
		}
		else if(part(line,sign,sign+2)==">="){
			constant = ">=";
			children[1] = new node("expr",part(line,sign+2,line.length()),temp);
		}
		else if(part(line,sign,sign+2)=="<="){
			constant = "<=";
			children[1] = new node("expr",part(line,sign+2,line.length()),temp);
		}
		else if(line[sign]=='>'){
			constant = ">=";
			children[1] = new node("expr",part(line,sign+1,line.length()),temp);
		}
		else if(line[sign]=='<'){
			constant = "<=";
			children[1] = new node("expr",part(line,sign+1,line.length()),temp);
		}
		else{
			constant = "<=";
			children[1] = new node("expr",part(line,sign+1,line.length()),temp);
			to_return = true;
		}
	}

	if(constant=="<="){
		for(int i=0;i<=nVariables;i++){
			children[0]->expression[i] = children[0]->expression[i]-children[1]->expression[i];
			children[1]->expression[i] = 0;
		}
	}
	else{
		constant = "<=";
		for(int i=0;i<=nVariables;i++){
			children[0]->expression[i] = children[1]->expression[i]-children[0]->expression[i];
		}
	}
	delete children[1];
	children.resize(1);
	return to_return;
}

/*

	processes this node, given it is of type boolean expression
	
*/
void node::proc_bexpr(){
	constant = "or";
	skip_spaces(begin,end);
	int OR = -1;
	for(int i=begin+1;i<end-2;++i){
		if(part(program,i,i+2)=="or" and isspace(program[i-1]) and isspace(program[i+2])){
			OR = i;
			break;
		}
	}
	if(OR==-1){
		node* ch = new node("affexpr",begin,end);
		children.pb(ch);
	}
	else{
		node* ch = new node("affexpr",begin,OR);
		children.pb(ch);
		int begin_backup = begin;
		begin = OR+2;
		proc_bexpr();
		begin = begin_backup;
	}
}

/*

	processes this node, given it is of type non deterministic (in general) boolean expression
	
*/
void node::proc_ndbexpr(){
	skip_spaces(begin,end);
	if(part(program,begin,end)=="*"){
		constant = "star";
		return;
	}
	if(part(program,begin,begin+4)=="prob"){
		constant = "prob";
		int open = -1,close = -1;
		for(int i=begin;i<end;++i){
			if(program[i]=='('){
				open = i;
			}
			else if(program[i]==')'){
				close = i;
				break;
			}
		}
		if(open==-1 or close==-1){
			cerr<<"Invalid probability"<<endl;
		}
		node* ch = new node("constant",open+1,close);
		children.pb(ch);
		return;
	}
	constant = "single bexpr";
	children.resize(1);
	children[0]=new node("bexpr",begin,end);
}

/*

	This is called after the constructor.
	calls the relevant proc_ function, depending on the type of the node.
	It give parsing the relevant recursive strategy to proceed with
	
*/
void node::process(int s, int l, bool negate){
	if(type=="stmt"){
		proc_stmt(s,l);
	}
	else if(type=="affexpr"){
		proc_affexpr();
	}
	else if(type=="expr"){
		proc_expr();
	}
	else if(type=="bexpr"){
		proc_bexpr();
	}
	else if(type=="literal"){
		proc_literal(negate);
	}
	else if(type=="ndbexpr"){
		proc_ndbexpr();
	}
	else if(type=="pvar"){
		proc_pvar();
	}
	else if(type=="constant"){
		proc_constant();
	}
	else if(type=="assgn"){
		proc_assgn(s,l);
	}
	else{
		cerr<<"Undefined type between "<<begin<<" "<<end<<endl<<part(program,begin,end)<<endl;
	}
}

/*

	A preprocessing function, to read the variable declaration in the program.
	The code needs the number of variables and their names before starting parsing, hence this function
	
*/
int find_variables(int& begin, int &end){
	int toReturn = 0;
	if(part(program,begin,begin+3)!="var"){
		cerr<<"No variables specified"<<endl;
		exit(0);
	}
	int semicolon = -1;
	for(int i=begin;i<end;i++){
		if(program[i]==';'){
			semicolon = i;
			break;
		}
	}
	if(semicolon==-1){
		cerr<<"No semicolon in program";
		exit(0);
	}
	istringstream ss(part(program,begin+3,semicolon));
	string token;
	while(getline(ss,token,',')){
		skip_spaces(token);
		toReturn++;
		variable[toReturn] = token;
		variableId[token] = toReturn;
	}
	begin = semicolon+1;
	return toReturn;
}

/*

	Prints the contents of the node
	outputfile: pointer to the stream in which the contents are printed
	and_string: The string which is used to represent and, ex: "&&" or "and"
	or_string: The string which is used to represent or, ex: "||" or "or"
	multiply_string: The string which is used to represent the multiplication symbol, ex: "*" or ""
	bruteforce: a misleading name, (because of code's history :p) but this means whether the strict inequalities should be printed as such or their non-strict appriximations should be printed
	
*/
void node::print(ostream& outputfile, string and_string, string or_string, string multiply_string, bool bruteforce){
	if(type=="expr"){
		bool something_printed = false;
		if(expression[0]!=0.0){
			outputfile<<expression[0];
			something_printed = true;
		}
		for(int i = 1;i<=nVariables;i++){
			if(expression[i]!=0.0){
				if(expression[i]>0.0){
					if(something_printed==true){
						outputfile<<"+"<<expression[i]<<multiply_string<<variable[i];
					}
					else{
						outputfile<<expression[i]<<multiply_string<<variable[i];
					}
					something_printed = true;
				}
				else{
					outputfile<<expression[i]<<multiply_string<<variable[i];
					something_printed = true;
				}
			}
		}
		if(!something_printed){
			outputfile<<"0";
		}
		return;
	}
	else if(type=="literal"){
		children[0]->print(outputfile,and_string,or_string,multiply_string,bruteforce);
		if(strict and bruteforce){
			if(constant=="<="){
				outputfile<<"<0";
			}
			else{
				outputfile<<">0";				
			}
		}
		else{
			outputfile<<constant<<"0";
		}
		return;
	}
	else if(type=="affexpr"){
		children[0]->print(outputfile,and_string,or_string,multiply_string,bruteforce);
		for(int i=1;i<children.size();++i){
			outputfile<<" "<<and_string<<" ";
			children[i]->print(outputfile,and_string,or_string,multiply_string,bruteforce);
		}
		return;
	}
	else if(type=="bexpr"){
		children[0]->print(outputfile,and_string,or_string,multiply_string,bruteforce);
		for(int i=1;i<children.size();++i){
			outputfile<<" "<<or_string<<" ";
			children[i]->print(outputfile,and_string,or_string,multiply_string,bruteforce);
		}
		return;
	}
	else if(type=="ndbexpr"){
		if(constant=="single bexpr"){
			children[0]->print(outputfile,and_string,or_string,multiply_string,bruteforce);
		}
		else{
			// <flag>
		}
	}
	else if(type=="stmt"){
		if(constant=="skip"){
			// Do nothing
		}
		else if(constant=="several statements"){
			children[0]->print(outputfile,and_string,or_string,multiply_string,bruteforce);
			outputfile<<endl;
			children[1]->print(outputfile,and_string,or_string,multiply_string,bruteforce);
		}
		else if(constant=="while"){
			outputfile<<"while(";
			children[0]->print(outputfile,and_string,or_string,multiply_string,bruteforce);
			outputfile<<"){\n\n";
			children[1]->print(outputfile,and_string,or_string,multiply_string,bruteforce);
			outputfile<<"\n}";
		}
		else if(constant=="if"){
			outputfile<<"if(";
			children[0]->print(outputfile,and_string,or_string,multiply_string,bruteforce);
			outputfile<<"){\n\n";
			children[1]->print(outputfile,and_string,or_string,multiply_string,bruteforce);
			outputfile<<"\n}\nelse{\n\n";
			children[2]->print(outputfile,and_string,or_string,multiply_string,bruteforce);
			outputfile<<"\n}";
		}
		else if(constant=="single assgn"){
			children[0]->print(outputfile,and_string,or_string,multiply_string,bruteforce);
			cout<<";\n";
		}
		else{
			cerr<<"Wrong constant in statement node\n";
		}
	}
	else if(type=="assgn"){
		children[0]->print(outputfile,and_string,or_string,multiply_string,bruteforce);
		outputfile<<" = ";
		if(constant=="assignment from distribution"){
			// <flag>
		}
		else if(constant=="simple assignment"){
			children[1]->print(outputfile,and_string,or_string,multiply_string,bruteforce);
		}
		else{
			cerr<<"Some wrong constant type in assignment\n";
		}
	}
	else if(type=="pvar" || type=="constant"){
		outputfile<<constant;
	}
}

/*

	The default constructor for an edge in the CFG

*/
CFG_edge::CFG_edge(){
	guard = NULL;
	next = NULL;
	toChange = 0;
	change = NULL;
	probability = 1.0;
}

/*

	A constructor for CFG_edge when every parameter is specified, which is generally the case
	next1: The destination of the CFG edge
	toChange1: The id of variable changed in this transition, it is 0 otherwise. 0 means constant being changed which anyways doesn't make any sense
	change1: the pointer to a expr node which represents the RHS of the assignment
	guard1: the guard of this transition, a bexpr node
	probability: probability of this transition occuring
	For probabilistic nodes, guard is true, and probability defines the transition

*/
CFG_edge::CFG_edge(CFG_location* next1,int toChange1,node* change1,node* guard1,double probability1){
	next = next1;
	toChange = toChange1;
	change = change1;
	guard = guard1;
	probability = probability1;
}

/*

	Prints the CFG_edge contents in some fashionable way
	Used for debugging only in this program

*/
void CFG_edge::print(bool print_probability){
	if(next!=NULL){
		cout<<"Destination: "<<next->label<<endl;
	}
	else{
		cout<<"Error! Error! Error!"<<endl;
	}
	if(change!=NULL){
		cout<<"Change: "<<variable[toChange]<<" = ";
		change->print();
		cout<<endl;
	}
	if(guard!=NULL){
		cout<<"Guard is: ";
		guard-> print();
		cout<<endl;
	}
	if(print_probability){
		cout<<"Probability to occur is "<<probability<<endl; 
	}
}

/*

	Constructor for a node in CFG, or a CFG location
		label: the id of CFG_location
		type: the type of CFG_node, "det" or "prob" or "ndet"

*/
CFG_location::CFG_location(string type,int label){
	this->label = label;
	this->type = type;
	invariant = NULL;
}

/*

	Prints the details about the CFG_location

*/
void CFG_location::print(){
	cout<<"Type: "<<type<<endl;
	cout<<"Invariant: ";
	if(invariant!=NULL){
		invariant->print();
	}
	else{
		cout<<"false";
	}
	cout<<endl;
	cout<<"LexRSM: ";
	for(int i=0;i<lexrsm.size();++i){
		bool printed = false;
		if(lexrsm[i][0]!=0.0){
			cout<<lexrsm[i][0];
			printed = true;
		}
		for(int j=1;j<=nVariables;++j){
			if(lexrsm[i][j]>0){
				if(printed==true){
					cout<<"+";
				}
				cout<<lexrsm[i][j]<<"*"<<variable[j];
				printed = true;
			}
			else if(lexrsm[i][j]<0){
				cout<<lexrsm[i][j]<<"*"<<variable[j];
				printed = true;
			}
		}
		if(printed == false){
			cout<<"0";
		}
		if(i!=lexrsm.size()-1){
			cout<<" ; ";
		}
	}
	cout<<endl;
	int i=1;
	for(vector<CFG_edge>::iterator it = edges.begin();it!=edges.end();++it){
		cout<<">>Edge #"<<i<<endl;
		it->print(type=="prob");
		i++;
	}
}