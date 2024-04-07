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
	ofstream programfile;
	programfile.open("example.prob");
	programfile<<"var x,y";
	cout<<"Input a value of n(>=0):\n";
	int n;
	cin>>n;
	nVariables = n;
	for(int i=1;i<=n;++i){
		variable[i] = "y"+to_string(i);
		variableId["y"+to_string(i)] = i;
	}
	for(int i=1;i<=n;i++){
		programfile<<",y"<<i;
	}
	programfile<<";\nwhile x>=0 and y>=0 do\n\nif * then x:=x-1; y:=2*y else y:=y-1 fi";
	if(n==0){
		programfile<<"\n\n";
	}
	else{
		programfile<<";\n\n";
		bool temp;
		node* condition = new node("bexpr","y1<=0;y1>=0",temp);
		for(int i=2;i<=n;++i){
			node* temp_condition = new node("bexpr","y" + to_string(i) + "<=0;y" + to_string(i) + ">=0",temp);
			condition = and_node(condition,temp_condition);
		}
		for(int i=0;i<condition->children.size();++i){
			if(i!=0){
				programfile<<"else\n";
			}
			programfile<<"if ";
			condition->children[i]->print(programfile,"and","or","*");
			programfile<<" then skip";
			programfile<<endl;
		}
		programfile<<"else skip\n";
		for(int i=0;i<condition->children.size();++i){
			programfile<<"fi";
			programfile<<endl;
		}
		// for(int i=0;i<condition->children.size();++i){
		// 	if(i!=0){
		// 		programfile<<";\n";
		// 	}
		// 	programfile<<"if ";
		// 	condition->children[i]->print(programfile,"and","or","*");
		// 	programfile<<" then skip else skip fi";
		// }
	}

	programfile<<"\n\nod"<<endl;
	programfile.close();

	// system("./a.out < example.prob > large_output");
}