A ***HashHeap*** is a data structure that merges a priority heap with
a hash table.  One of the drawbacks of priority queues implemented with
binary heaps is that searching requires O(n) time. Other operations
such as arbitrary removal or replacement of values thus also require O(n).
Consider the possibility that the priority of objects can *change.*
This would require finding the object then moving it up or down the
queue.  With most implementations of priority heaps this is only
possible by removing the previous value and inserting a new one.
<br>

In a HashHeap, however, values are paired with keys. The keys are
hashable (`:Hash+Eq`) and the values are comparable (`:Ord`).
Conceptually, an internal HashMap maps keys to *indices* of where
values are stored inside an internal vector. Heap operations that
require values to be swapped must keep the hashmap consistent.
While the actual implementation is a bit more complicated, as it avoids
all cloning and Rc's, this arrangement allows search to be completed in
(avearge-case) O(1) time.  Removing or replacing a value, which will
also require values to be swapped up or down the heap, can be done in
O(log n) time. 
