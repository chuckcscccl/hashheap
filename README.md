A ***HashHeap*** is a data structure that merges a priority heap with
a hash table.  One of the drawbacks of priority queues implemented with
binary heaps is that searching requires O(n) time. Other operations
such as arbitrary removal or replacement of values thus also require O(n).
<br>

In a HashHeap, however, values are paired with keys. The keys are
hashable (`:Hash+Eq`) and the values are comparable (`:Ord`).
Conceptually, an internal HashMap maps keys to *indices* of where
values are stored inside an internal vector. Heap operations that
require values to be swapped must keep the hashmap consistent.
While the actual implementation is a bit more complicated, as it avoids
all cloning, this arrangement allows search to be completed in
(avearge-case) O(1) time.  Removing or replacing a value, which will
also require values to be swapped up or down the heap, can be done in
O(log n) time.
<br>

Consider the possibility that the priority of objects can *change.*
This would require finding the object then moving it up or down the
queue.  With most implementations of priority heaps this is only
possible by removing the previous value and inserting a new one.
A HashHeap can be used, for example, to effectively implement Dijkstra's
algorithm as the "open" or "tentative" queue.  When a lower-cost path
is found, its position in the queue must be updated.  This is possible
in O(log n) time with a HashHeap.

Examples:

```
  use hashheap::*;
  let mut priority_map = HashHeap::<&str,u32>::new_minheap();
  priority_map.insert("A", 4);   // O(1) average, O(log n) worst
  priority_map.insert("B", 2);
  priority_map.insert("C", 1);
  priority_map.insert("D", 3);
  priority_map.insert("E", 4);
  priority_map.insert("F", 5);
  priority_map.insert("A", 6);   // insert can also modify
  assert_eq!(priority_map.peek(), Some((&"C",&1))); // O(1)
  assert_eq!(priority_map.get(&"E"), Some(&4));     // O(1)
  assert_eq!(priority_map[&"F"], 5);                // O(1)
  priority_map.modify(&"F", |v|{*v=4;});            // O(log n)
  priority_map.remove(&"E");                        // O(log n)
  let mut total = 0;
  for (key,val) in &priority_map {
    total += val;
  }
  assert_eq!(total, 16);
  assert_eq!(priority_map.pop(), Some(("C",1)));    // O(log n)
  assert_eq!(priority_map.pop(), Some(("B",2)));
  assert_eq!(priority_map.pop(), Some(("D",3)));
  assert_eq!(priority_map.pop(), Some(("F",4)));    
  assert_eq!(priority_map.pop(), Some(("A",6)));    
  assert_eq!(priority_map.len(), 0);
```
