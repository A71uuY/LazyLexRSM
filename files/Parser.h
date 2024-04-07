#include <string>
using namespace std;

/*

	A class used to parse the program easily
	This helps in the recursive implementation of parsing

*/
struct node{
	string type; //The type of entity that this node corresponds to
	string constant; //The constant factor (subtype) of this node
	bool strict; // For the literal nodes, this defines whether the inequality is strict or not
	int begin,end; //begin and end point in program
	vector<node *> children; //children in the parse tree, the order of children is custom wrt the type of node
	node *bracket; //bexpr written in bracket next to this node (for stmt only), it helps to store the invariant if any was present in the initial program description
	vector<double> expression; //for expressions only, it stores the coefficient vector of the corresponfing expression
	double delta; // For the expressions in which a probabilistic assignment is there, this is the padding which has to be applied on the either side of rhs value
	bool not_uni;
	double lb;
	double ub;
	bool l_bounded;
	bool r_bounded;
	//constructors
	node(string t);
	node(string t, int b, int e, int s = 0, int l = 0, bool negate = false);
	node(string t, string line, bool& to_return);
private:
	
	//procs
	void proc_stmt(int s,int l);
	void proc_assgn(int s,int l);
	void proc_affexpr(); //
	void proc_pvar();
	void analyse_expr(int begin,int end,bool negate);
	void analyse_expr(string l,bool negate);
	void proc_expr(); //
	void proc_expr(string l); //
	void proc_constant();
	bool proc_literal(bool negate, bool strategic = true, string line = "");
	void proc_bexpr(); //
	void proc_ndbexpr();
	void form_vector(int begin,int end,bool negate);
	void form_vector(string l,bool negate);
	
	//main process
	void process(int s, int l, bool negate);
public:
	void print(ostream& outputfile = cout,string and_string = "and", string or_string = "or", string multiply_string = "", bool bruteforce = false);
};

/*

	A node in the CFG

*/
struct CFG_location;

/*

	An edge (directed) in the CFG

*/
struct CFG_edge{
public:
	CFG_location* next;
	int toChange;
	node* change; // An expr node
	node* guard; // A bexpr node
	double probability;
	CFG_edge();
	CFG_edge(CFG_location* next,int toChange,node* change,node* guard=NULL,double probability=1.0);
	void print(bool print_probability = false);
};

struct CFG_location{
public:
	CFG_location(string type,int label);
	int label;	// The label of this node, or the reverse mapping of what is stored in the "label_map" map
	string type; // det ndet or prob
	vector<CFG_edge> edges; // The set of edges that emerge from this node
	vector<int> ranking_function; // The coefficient matrix for the affine ranking function for this node
	node* invariant; // A bexpr node, the invariant at this particular node
	void print();
	vector<vector<double> > lexrsm;
};

void skip_spaces(int &begin, int &end);
void skip_spaces(string& line);
void vcopy(vector<node*> &sink,vector<node*> &tocopy);
node* negation(node* tonegate);
node* and_node(node* one,node* two);
int find_variables(int& begin, int& end);

//extern because these variables are needed in main file also
extern string program; // The program which is to be parsed
extern int nVariables; // The number of Variables being used in the program, is also the (dimension-1) of any expression vector in "expr" nodes
extern int last_used_label; // Keeps a track of the number of CFG_location labels used
extern map<int,CFG_location*> label_map; // Maps the id's of the node to the pointer to their CFG_location instance
extern node* root; // The root node of the entire parsed form of the program
extern map<string,int> variableId; // Maps the variable names to their id's. Needed because program wants to see the variables as number not strings
extern map<int,string> variable; // Maps the variable id's to the variable names
extern int dummy_states_needed; //For adding the if * condition in fast file