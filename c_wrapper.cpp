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
#include "files/Parser.h"
using namespace std;
#define MAXL 100000 //Maximum length of the program
#define part(x,a,b) (x.substr((a),((b)-(a))))
#define pb push_back


int main(){
	int start,end;
	char input[MAXL];
	// Setting precision to the printing of the double variables in program
	// cout<<fixed<<setprecision(10);
	int r,i;
	for(i=0;(r=getchar())!=EOF;i++)
		input[i]=r;
	input[i]=0;
	program=input;
	int begin = 0;
	int endprog = program.length();
	skip_spaces(begin,endprog);
	nVariables = find_variables(begin,endprog); //To find the number of different variables of the type x_i in the program
	start = ++last_used_label;
	end = ++last_used_label;
	label_map[start] = new CFG_location("det",start);
	label_map[end]	 = new CFG_location("det",end);
	// Code for adding self loop
	// CFG_edge last_edge(label_map[end],-1,NULL);
	// label_map[end]->edges.pb(last_edge);
	root=new node("stmt",begin,endprog,start,end);
	cout<<"int main(){\n\n";
	cout<<"int "<<variable[1];
	for(int i=2;i<=nVariables;i++){
		cout<<","<<variable[i];
	}
	// Ask Petr <flag> whether all the variables are integers or double because otherwise double causes problems for c2fsm
	cout<<";\n";
	root->print(cout,"&&","||","*",true);
	cout<<"\n}\n";
	return 0;
}