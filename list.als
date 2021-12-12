module list[Time]

open util/ordering[Time] as o

// o/nxt - not my
// this/nxt or nxt- my

// open elem_order[Time]
// there will be something like header file in c++ prog

// A signature in Alloy is similar to the signature of a schema
// in that it defines the vocabulary for the model.
sig List { root: Node lone -> Time }
sig Node { nxt: Node lone -> Time}

// A Node can be is its own successor. The nxt fact will fix it:
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
