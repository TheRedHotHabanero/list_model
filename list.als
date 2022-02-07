module list[Time]

open util/ordering[Time] as o

// o/nxt - not my
// this/nxt or nxt- my

// open elem_order[Time]
// there will be something like header file in c++ prog

// A signature in Alloy is similar to the signature of a schema
// in that it defines the vocabulary for the model.
var sig Node { var nxt: set Node }

var sig Root in Node {}

fact
{
  always
  {
    Root = Node - Node.^nxt // все узлы, которые достижимы из каких-то узлов

  }
}

// A Node can be is its own successor. The nxt fact will fix it:
// лучше выносить в предикаты валидности.
/*
fact nxt_not_reflexive
{
  all t: Time |
  no n:Node   | n = n.(nxt.t)
}

// There are Nodes that do not belong to to exactly one list.
// The next fact will fix it:
fact all_nodes_belong_to_one_list
{
  all t: Time |
  all n: Node | one q:List | n in q.(root.t).*(nxt.t)
}

// Fact to prevent a cycle:
fact next_not_cyclic
{
  all t: Time |
  no n: Node  | n in n.^(nxt.t)
}
*/
fun nodes(list: Node) : Node
{
  //{n: Node | n in lst.*(nxt + ~nxt)} //inverse
  list.*(nxt + ~nxt)
}

fun root(list: Node) : Node
{
  Root & list.nodes
}

fun last(list: Node) : Node
{
  { n: list.nodes | no n.nxt }
}

/*
// Returns all nodes in the list at a given time
fun elems(l: List, t: Time): set Node
{
  (l.root.t).*(nxt.t)
}

// Returns the last element from the list
fun last(l: List, t: Time) : one Node
{
  // Got a root node
  let elts = l.elems[t]
  {
    // Took all the elements at some point in time in some list &
    // & subtract all of them that have the next
    elts - (nxt.t).elts
  }
}

pred empty(l: List, t: Time)
{
  no l.root.t
}

pred join(l1, l2: List, now: Time)
{
  let future = now.next
  {
    // All nodes that belong to l2 belong to l1
    let last = l1.last[now]
    {
      let head = l2.root.now
      {
        l2.empty[future]
        l1.elems[future] = l1.elems[now] + l2.elems[now]

        // Set the order
        nxt.future = nxt.now + (last -> l2.root.now)
      }
    }
  }
}

pred show_join()
{
  all t: Time - last
  {
    some disj l1, l2: List
    {
      join[l1, l2, t]
    }
  }
}

pred show() {}
run show_join for 5 but 2 Time
*/

pred valid(lst: Node)
{
  all n: lst.nodes
  {
    lone n.nxt
    lone nxt.n //prev in fact
    n not in n.^nxt
  }
  one lst.root
}

pred all_valid()
{
  //all r: Root | r.valid
  all n:Node | n.valid
}

pred join(r1, r2: Root)
{
  no r1.nodes & r2.nodes
  let l1 = r1.last
  {
    nxt' = nxt + l1 -> r2
    Node' = Node
    Root' = Root - r2
  }
}

run
{
  all_valid
  some r1, r2 : Root | join[r1, r2]
  after always {nxt' = nxt and Node' = Node and Root' = Root}
} for 5

assert prop1
{
  always
  {
    {
      all_valid
      some disj r1, r2: Root | join[r1, r2]
    }
    implies
    {
      after all_valid
    }
  }
}
check prop1 for 5