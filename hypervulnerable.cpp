#include <bits/stdc++.h>
//# define int long long

// note that 'E' is reserved for epsilon transition and hence its use should be avoided in the language
// numbering of states start from 0 (keeping in mind the existence of q0)
const char eps = 'E'; // null/empty transition
using namespace std;

struct nfa
{
    // NFA A = (Q,sigma, delta, q0,F)
    vector<int> q;                    // vector of states
    set<char> lan;                    // set of language characters
    set<tuple<int, char, int>> trans; // transition states
    int q0;                           // starting state
    set<int> f;                       // set of final states
};

void PrintNFA(nfa a)
{
    cout << "States in the attack automaton - "
         << "\n";
    for (auto &x : a.q)
    {
        cout << x << " ";
    }
    cout << "\n";
    cout << "Start state of attack automaton - " << a.q0 << "\n";
    cout << "\n";
    cout << "Final states of attack automaton - "
         << "\n";
    for (auto &x : a.f)
    {
        cout << x << " ";
    }
    cout << "\n";
    cout << "Transitions in the attack automaton - "
         << "\n";
    for (auto &x : a.trans)
    {
        cout << get<0>(x) << " " << get<1>(x) << " " << get<2>(x) << "\n";
    }
    cout << "\n";
}

nfa comp(nfa a)
{
    nfa a_;
    for (auto x : a.q)
    {
        bool pres = false;
        for (auto y : a.f)
        {
            if (x == y)
            {
                pres = true;
                break;
            }
        }
        if (!pres)
            a_.f.insert(x);
    }
    a_.lan = a.lan;
    a_.q = a.q;
    a_.q0 = a.q0;
    a_.trans = a.trans;
    return a_;
}
nfa un(nfa a, nfa b)
{
    if (a.q.empty())
        return b;
    if (b.q.empty())
        return a;
    nfa ans;
    sort(a.q.begin(), a.q.end());
    sort(b.q.begin(), b.q.end());
    int sizeA = a.q.size();
    int sizeB = b.q.size();

    // states mapping for A U B
    for (int i = 0; i < sizeA * sizeB; i++)
        ans.q.push_back(i);

    // start state for A U B
    int startA = lower_bound(a.q.begin(), a.q.end(), a.q0) - a.q.begin();
    int startB = lower_bound(b.q.begin(), b.q.end(), b.q0) - b.q.begin();
    ans.q0 = (startA)*sizeB + startB;

    // language remains the same
    ans.lan = a.lan;

    // final states of A U B
    for (auto &fA : a.f)
    {
        int i = lower_bound(a.q.begin(), a.q.end(), fA) - a.q.begin();
        for (int &sB : b.q)
        {
            int j = lower_bound(b.q.begin(), b.q.end(), sB) - b.q.begin();
            ans.f.insert(i * sizeB + j);
        }
    }

    for (auto &fB : b.f)
    {
        int j = lower_bound(b.q.begin(), b.q.end(), fB) - b.q.begin();
        for (int &sA : a.q)
        {
            int i = lower_bound(a.q.begin(), a.q.end(), sA) - a.q.begin();
            ans.f.insert(i * sizeB + j);
        }
    }

    // building the transition function for A U B
    //	a.lan.insert('E');
    for (auto ch : a.lan)
    {
        map<int, set<int>> relA, relB;
        for (auto x : a.trans)
        {
            if (get<1>(x) == ch)
            {
                relA[get<0>(x)].insert(get<2>(x));
                //         		if (ch==eps) relA[get<0>(x)].insert(get<0>(x));
            }
        }
        for (auto x : b.trans)
        {
            if (get<1>(x) == ch)
            {
                relB[get<0>(x)].insert(get<2>(x));
                //         		if (ch==eps) relB[get<0>(x)].insert(get<0>(x));
            }
        }

        for (auto pair1 : relA)
        {
            for (auto pair2 : relB)
            {
                int i = lower_bound(a.q.begin(), a.q.end(), pair1.first) - a.q.begin();
                int j = lower_bound(b.q.begin(), b.q.end(), pair2.first) - b.q.begin();
                for (auto stateA : pair1.second)
                {
                    for (auto stateB : pair2.second)
                    {
                        int i1 = lower_bound(a.q.begin(), a.q.end(), stateA) - a.q.begin();
                        int j1 = lower_bound(b.q.begin(), b.q.end(), stateB) - b.q.begin();
                        ans.trans.insert(make_tuple(i * (sizeB) + j, ch, i1 * (sizeB) + j1));
                    }
                }
            }
        }
    }

    return ans;
}
nfa inter(nfa a, nfa b)
{
    // calculated using DeMorgans Law
    nfa a_ = comp(a);
    nfa b_ = comp(b);
    nfa ans = comp(un(a_, b_));
    return ans;
}

nfa concat(nfa a, nfa b)
{
    // a o b
    nfa ans;

    sort(a.q.begin(), a.q.end());
    sort(b.q.begin(), b.q.end());

    int sizeA = a.q.size();
    int sizeB = b.q.size();

    map<int, int> mapA;
    map<int, int> mapB;

    // normalizing nfa a
    for (int i = 0; i < sizeA; i++)
    {
        mapA[a.q[i]] = i;
        a.q[i] = i;
    }
    a.q0 = mapA[a.q0];

    set<int> finA;
    for (auto &x : a.f)
        finA.insert(mapA[x]);
    a.f = finA;

    set<tuple<int, char, int>> trA;
    for (auto &x : a.trans)
        trA.insert(make_tuple(mapA[get<0>(x)], get<1>(x), mapA[get<2>(x)]));
    a.trans = trA;
    //	PrintNFA(a);

    // normalizing nfa b
    for (int i = 0; i < sizeB; i++)
    {
        mapB[b.q[i]] = i + sizeA;
        b.q[i] = i + sizeA;
    }
    b.q0 = mapB[b.q0];

    set<int> finB;
    for (auto &x : b.f)
        finB.insert(mapB[x]);
    b.f = finB;

    set<tuple<int, char, int>> trB;
    for (auto &x : b.trans)
        trB.insert(make_tuple(mapB[get<0>(x)], get<1>(x), mapB[get<2>(x)]));
    b.trans = trB;
    //	PrintNFA(b);

    //	cout<<"\n"<<"\n"<<"\n";

    // forming a o b
    for (int i = 0; i < sizeA + sizeB; i++)
        ans.q.push_back(i);

    ans.q0 = a.q0;

    ans.f = b.f;

    ans.trans = a.trans;
    for (auto &x : b.trans)
        ans.trans.insert(x);

    ans.lan = a.lan;

    for (auto &x : a.f)
    {
        for (auto &y : b.trans)
        {
            if (get<0>(y) == b.q0)
                ans.trans.insert(make_tuple(x, get<1>(y), get<2>(y)));
        }
    }

    return ans;
}

nfa LoopBack(nfa a, int pivot, char ch, int state)
{

    // q* is treated as the minimum excludent of a.q
    sort(a.q.begin(), a.q.end());
    int qStar = a.q.size();
    for (int i = 0; i < a.q.size(); i++)
    {
        if (a.q[i] != i)
        {
            qStar = i;
            break;
        }
    }
    a.q.push_back(qStar);
    a.trans.insert(make_tuple(qStar, ch, state));
    a.q0 = qStar;
    a.f.clear();
    a.f.insert(pivot);
    return a;
}

nfa AttackForPivot(nfa a, int state)
{
    nfa ans;
    map<char, vector<int>> m;
    for (auto &transition : a.trans)
    {
        if (get<0>(transition) == state)
        {
            m[get<1>(transition)].push_back(get<2>(transition));
        }
    }
    for (auto &x : m)
    {
        auto ch = x.first;
        auto vec = m[ch];
        for (int i = 0; i < vec.size(); i++)
        {
            for (int j = i + 1; j < vec.size(); j++)
            {
                //            	cout<<"call";
                nfa a1 = LoopBack(a, state, ch, vec[i]);
                nfa a2 = LoopBack(a, state, ch, vec[j]);
                nfa ap = a;
                ap.f.clear();
                ap.f.insert(state);
                //                PrintNFA(ap);
                nfa as = a;
                as.q0 = state;
                //                PrintNFA(comp(as));
                // PrintNFA(concat((concat(ap,inter(a1,a2))),comp(as)));
                ans = un(ans, concat((concat(ap, inter(a1, a2))), comp(as)));
                //                PrintNFA(inter(a1,a2));
            }
        }
    }
    return ans;
}

// AttackAutomaton function
nfa AttackAutomaton(nfa a)
{
    nfa ans;
    for (auto &state : a.q)
    {
        auto aI = AttackForPivot(a, state);
        ans = un(ans, aI);
    }
    return ans;
}

nfa StateReduction(nfa a){
	if (a.q.empty()) return a;
	int n = a.q.size();
	
	// adjacency list of all nodes
	vector < set <int> > adj(n+1);
	int visit[n+1]={0};
	
	for (auto &x : a.trans){
		adj[get<0>(x)].insert(get<2>(x));
	}
	
	set<int> toBeVis;
	toBeVis.insert(a.q0);
	
	map <int, int> newStates;
	int ctr = 0;
	
	// visiting the connected component of the nfa starting with starting node
	while(!toBeVis.empty()){
		int state = *toBeVis.begin();
		newStates[state] = ctr++;
		visit[state] = 1;
		for (auto &x : adj[state]){
			if (!visit[x]) 
				toBeVis.insert(x);
		}
		toBeVis.erase(toBeVis.find(state));
	}
	
	nfa ans;
	
	// keeping the lang same
	ans.lan = a.lan;
	
	// building the transition function
	for (auto &x : a.trans){
		if (visit[get<0>(x)]){
			ans.trans.insert(make_tuple(newStates[get<0>(x)], get<1>(x), newStates[get<2>(x)]));
		}
	}
	
	// storing the reduced states
	for (int i=0; i < ctr; i++) ans.q.push_back(i);
	
	// assigning the start state
	ans.q0 = newStates[a.q0];
	 
	// assigning the final states
	for (auto &x : a.f){
		if (visit[x]) 
	    	ans.f.insert(newStates[x]);
	} 
	
	return ans;
}

int main()
{
    nfa inp;
    cout << "Avoid NFAs with epsilon transitions"
         << "\n"
         << "\n";

    cout << "Enter the number of characters in NFA language"
         << "\n";
    int l;
    cin >> l;
    cout << "Now in the next 'l' lines, enter the characters -"
         << "\n";
    char ch;
    while (l--)
    {
        cin >> ch;
        inp.lan.insert(ch);
    }
    cout << "Enter the number of states in the input NFA (n)- "
         << "\n";
    int n;
    cin >> n;
    cout << "Now in the next 'n' lines, enter the nodes (not in any particular order) -"
         << "\n";
    int x;
    while (n--)
    {
        cin >> x;
        inp.q.push_back(x);
    }

    cout << "Enter the start state -"
         << "\n";
    int st;
    cin >> st;
    inp.q0 = st;

    cout << "Enter the number of final states in the input NFA (m)- "
         << "\n";
    int m;
    cin >> m;
    cout << "Now in the next 'm' lines, enter the final nodes (accepting nodes) (not in any particular order) -"
         << "\n";
    int y;
    while (m--)
    {
        cin >> y;
        inp.f.insert(y);
    }

    cout << "Enter the number of transitions in the input NFA (t)- "
         << "\n";
    int t;
    cin >> t;
    cout << "Now in the next 't' lines, enter the transitions in the form of (starting node (int), character (char), end node (int)) -"
         << "\n";
    int a, b;
    char c;
    while (t--)
    {
        cin >> a >> c >> b;
        inp.trans.insert(make_tuple(a, c, b));
    }
    // for (auto &x : inp.trans){
    //	cout<<get<0>(x)<<" "<<get<1>(x)<<" "<<get<2>(x)<<"\n";
    // }

    nfa out = AttackAutomaton(inp);
    nfa ans = StateReduction(out);
    PrintNFA(ans);

    return 0;
}