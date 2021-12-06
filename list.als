module list[Time]

// open elem_order[Time]

// there will be something like header file in c++ prog

// A signature in Alloy is similar to the signature of a schema
// in that it defines the vocabulary for the model.
sig List { root: lone Node }
sig Node { next: lone Node }

// A Node can be is its own successor. The next fact will fix it:
fact next_not_reflexive { no n:Node | n = n.next }

// There are Nodes that do not belong to to exactly one list. The next fact will fix it:
fact all_nodes_belong_to_one_list
{ all n:Node | one q:List | n in q.root.*next }

// Fact to prevent a cycle:
fact next_not_cyclic { no n:Node | n in n.^next }

pred show() {}
run show for 3


