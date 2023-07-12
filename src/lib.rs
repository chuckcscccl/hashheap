//! A ***[HashHeap]*** is a data structure that merges a priority heap with
//! a hash table.  One of the drawbacks of priority queues implemented with
//! binary heaps is that searching requires O(n) time. Other operations
//! such as arbitrary removal or replacement of values thus also require O(n).
//!

//! In a HashHeap, however, values are paired with keys. The keys are
//! hashable (`:Hash+Eq`) and the values are comparable (`:Ord`).
//! Conceptually, an internal HashMap maps keys to *indices* of where
//! values are stored inside an internal vector. Heap operations that
//! require values to be swapped must keep the hashmap consistent.
//! While the actual implementation is a bit more complicated, as it avoids
//! all cloning, this arrangement allows search to run in
//! (avearge-case) O(1) time.  Removing or replacing a value, which will
//! also require values to be swapped up or down the heap, can be done in
//! O(log n) time.
//! <br>
//!

//! Consider the possibility that the priority of objects can *change.*
//! This would require finding the object then moving it up or down the
//! queue.  With most implementations of priority heaps this is only
//! possible by removing the previous value and inserting a new one.
//! A HashHeap can be used, for example, to effectively implement Dijkstra's
//! algorithm as the "open" or "tentative" queue.  When a lower-cost path
//! is found, its position in the queue must be updated.  This is possible
//! in O(log n) time with a HashHeap.

//!
//! **The main documentation for this create are found under struct [HashHeap].**
//!
//! Because the mutation of values will require them to be repositioned in
//! the heap, certain expected methods are not available, including `get_mut`
//! and `iter_mut`.  Instead, a [HashHeap::modify] function is provided that
//! allows the mutation of values with a closure, and will automatically
//! adjust their positions afterwards.
//!
//! Concerning the time complexity of operations, we consider looking up a
//! hash table to be an O(1) operation, although theoretically it can be
//! worst-case O(n) with concocted examples.  They rarely occur in practice.
//! Thus all complexities are given as average case, unless otherwise noted.
//! On the other hand, worst-case scenarios for binary heaps occur easily,
//! so we note both the average and worst-case complexities when there's a
//! difference.
//!
//! Examples
//! ```
//! # use hashheap::*;
//!    let mut priority_map = HashHeap::<&str,u32>::new_minheap();
//!    priority_map.insert("A", 4);   // O(1) average, O(log n) worst
//!    priority_map.insert("B", 2);
//!    priority_map.insert("C", 1);
//!    priority_map.insert("D", 3);
//!    priority_map.insert("E", 4);
//!    priority_map.insert("F", 5);
//!    priority_map.insert("A", 6);   // insert can also modify
//!    assert_eq!(priority_map.peek(), Some((&"C",&1))); // O(1)
//!    assert_eq!(priority_map.get(&"E"), Some(&4));     // O(1)
//!    assert_eq!(priority_map[&"F"], 5);                // O(1)
//!    priority_map.modify(&"F", |v|{*v=4;});            // O(log n)
//!    priority_map.remove(&"E");                        // O(log n)
//!    assert_eq!(priority_map.pop(), Some(("C",1)));    // O(log n)
//!    assert_eq!(priority_map.pop(), Some(("B",2)));
//!    assert_eq!(priority_map.pop(), Some(("D",3)));
//!    assert_eq!(priority_map.pop(), Some(("F",4)));    
//!    assert_eq!(priority_map.pop(), Some(("A",6)));    
//!    assert_eq!(priority_map.len(), 0);
//! ```    
/*
Theory stuff:

For heap of size n there are always (n+1)/2 leaves
So there are n-(n+1)/2 = non-leaves, not same as (n-1)/2, because of remainder
*/

#![allow(dead_code)]
#![allow(unused_variables)]
#![allow(non_snake_case)]
#![allow(non_camel_case_types)]
#![allow(unused_parens)]
#![allow(unused_mut)]
#![allow(unused_assignments)]
#![allow(unused_doc_comments)]
#![allow(unused_imports)]
use std::collections::{HashMap,HashSet};
use std::collections::hash_map::RandomState;
use std::hash::{Hash,Hasher,BuildHasher};
use std::cmp::Ord;
use std::cell::{RefCell,Ref,RefMut};

const DEFAULTCAP:usize = 16;

//// independent functions for heap indices:
fn left(i:usize) -> usize { 2*i+1 }
fn right(i:usize) -> usize { 2*i+2 }
fn parent(i:usize) -> usize { if i>0 {(i-1)/2} else {0} }

fn derive_hash<T:Hash+Eq>(rs:&mut RandomState, key:&T) -> usize
{
   //let mut rs = hs.hasher() as & dyn std::hash::BuildHasher<Hasher:Hasher>;
   //let mut rs = RandomState::new();
   let mut bs = rs.build_hasher();
   key.hash(&mut bs);
   bs.finish() as usize
} // used by autohash


pub struct HashHeap<KT, VT>
{
   keys: Vec<Option<KT>>,  // None means once occupied
   vals : Vec<(VT,usize)>, // with inverse hash index (for map)
   userhash : Option<fn(&KT) -> usize>,
   rehash : fn(usize, usize) -> usize, // hashi,collisions -> newhashi
   kmap : HashMap<usize,(usize,usize)>, // hashindex to (ki,vi)
   lessthan : fn(&VT,&VT) -> bool,
   autostate : RefCell<RandomState>,
   minmax: bool, // record if it's min or max heap
}
impl<KT:Hash+Eq, VT:Ord> HashHeap<KT,VT>
{
  /// creates a HashHeap with given capacity.  If the capacity is less than 1,
  /// it defaults to 16.  If the second argument is true, a maxheap is
  /// created; otherwise a minheap is created.
  pub fn with_capacity(mut cap:usize, maxheap:bool) -> HashHeap<KT,VT> {
    if cap<1 {cap = DEFAULTCAP;}
    let mut hh = HashHeap {
      keys: Vec::with_capacity(cap),    
      vals: Vec::with_capacity(cap),
      kmap: HashMap::with_capacity(cap),
      userhash: None,
      rehash: |h,c|{h+c},
      lessthan : |a,b|a<b,
      autostate: RefCell::new(RandomState::new()),
      minmax: maxheap,
    };
    if !maxheap {hh.lessthan = |a,b|b<a;}
    hh
  }//with_capacity

  /// convenient way to create an empty min-hashheap with default capacity 16
  pub fn new_minheap() -> HashHeap<KT,VT> { Self::with_capacity(0,false) }
  /// convenient way to create an empty max-hashheap with default capacity 16  
  pub fn new_maxheap() -> HashHeap<KT,VT> { Self::with_capacity(0,true) }

  /// creates a min/max hashheap from a vector of key-value pairs.  This
  /// operation takes O(n) time, where n is the length of vector, as it uses
  /// the well-known *heapify* algorithm.  The second, bool argument determines
  /// if the heap portion of the structure is a maxheap (true) or minheap (false)
  pub fn from_pairs(kvpairs:Vec<(KT,VT)>, maxheap:bool) -> HashHeap<KT,VT> {
     let mut hh = Self::with_capacity(kvpairs.len()+1,maxheap);
     hh.heapify(kvpairs);
     hh
  }//from_pairs

  /// This function allows the user to override the default hasher
  /// provided by the Hash trait with an arbitrary function.  The
  /// operation is only allowed while the HashHeap is empty.  Returns
  /// true on success.
  pub fn set_hash(&mut self, h: fn(&KT)->usize) -> bool {
    if self.keys.len()>0 {return false;}
    self.userhash = Some(h);
    true
  }

  /// Override the default rehash method, which implements linear probing.
  /// The given function take the original hash value as the first
  /// argument and the number of collisions as the second argument.  The
  /// internal representation uses the hasher from the Hash trait to compute
  /// an index, which becomes the key to a hashmap from *indices* to locations
  /// of keys and values.  Collisions are therefore resolved by a rehashing.
  /// Example for setting a quadratic probing rehash function:
  /// ```
  /// # use hashheap::*;
  ///   let mut table = HashHeap::<&str,i32>::new_minheap();
  ///   table.set_rehash(|h,c|h+c*c/2 + c/2); 
  /// ```
  /// The calculated hash value does not index a vector but a rust HashMap with
  /// indices as keys, so there's no issue with out-of-bounds hash values.
  pub fn set_rehash(&mut self, rh: fn(usize,usize)->usize) -> bool {
    if self.keys.len()>0 {return false;}  
    self.rehash = rh;
    true
  }

  /// Override the internal comparison function with a function cmp such
  /// that `cmp(a,b)` is true means a is "less than" b.  This operation
  /// is only allowed when the size of the HashHeap is no more than one.
  /// Returns true on success.
  pub fn set_cmp(&mut self, cmp:fn(&VT,&VT)->bool) -> bool {
    if self.keys.len()>1 {false}
    else {
      self.lessthan = cmp;
      true
    }
  }//set_cmp

  fn autohash(&self, key:&KT) -> usize {
     self.userhash
         .map_or(derive_hash(&mut *self.autostate.borrow_mut(),key),
                 |f|{f(key)})  
  }//autohash


  // must return index of where key is found, or of an empty slot,
  // must rehash on collision
  fn findslot(&self, key:&KT) -> (usize,bool) {
    let mut h = self.autohash(key);
    let h0 = h;
    let mut collisions = 0;
    let mut reuse = None;
    while let Some((ki,vi)) = self.kmap.get(&h) {
      match &self.keys[*ki] {
        Some(key2) if key2 == key => { return (h,true); },
        None => { // rehash, set reuse
          if let None = reuse {reuse = Some(h);}
          collisions +=1;
          //self.tc+=1;
          h = (self.rehash)(h0,collisions);
        },
        Some(_) => {  //rehash, includes case where key entry is None
          collisions += 1;
          //self.tc+=1;
          h = (self.rehash)(h0,collisions);
        },
      }//match
    } //while let
    reuse.map_or((h,false), |g|(g,false))
  }//findslot returns index for insert, and bool indicating exact key match
   //Here, index refers to index of kmap, not of heap vector

  /// Add or change a key-value pair, returning the replaced pair, if
  /// it exists.  This operation runs in **average-case O(1) time and
  /// worst-case O(log n) time**.
  /// Insertion into a heap is known to be average-case O(1) because the
  /// number of values on each higher level decreases geometrically, so that
  /// the average is bounded by a convergent infinite series.
  pub fn insert(&mut self, key:KT, val:VT) -> Option<(KT,VT)> {
    let (h,exists) = self.findslot(&key);
    if exists {
      /* must replace value and reposition within heap !!!!!!!!!!! */
      let (ki,vi) = *self.kmap.get(&h).unwrap();
      let mut newkey = Some(key);
      let mut newval = (val,h);
      core::mem::swap(&mut newkey, &mut self.keys[ki]);
      core::mem::swap(&mut newval, &mut self.vals[vi]);
      self.reposition(vi);
      Some((newkey.unwrap(), newval.0))
    }//replace
    else {    // assuming key is new
      let kn = self.keys.len();
      let vn = self.vals.len();
      self.keys.push(Some(key));
      self.vals.push((val,h));
      self.kmap.insert(h,(kn,vn));
      self.swapup(vn);
      None
    }//else
  }//insert

  /// Version of insert that does not replace existing key.
  /// Instead, it returns false if an equivalent key already exists.
  pub fn push(&mut self, key:KT, val:VT) -> bool {
    let (h,exists) = self.findslot(&key);
    if exists { false }
    else {    // assuming key is new
      let kn = self.keys.len();
      let vn = self.vals.len();
      self.keys.push(Some(key));
      self.vals.push((val,h));
      self.kmap.insert(h,(kn,vn));
      self.swapup(vn);
      true
    }//else
  }//push

  /// This operation replaces the top (highest priority) entry
  /// with given key and value, and returns the previous top entry.
  /// However, if the given key already exists, it replaces the existing
  /// key-value with the new ones before removing the top entry.  This
  /// operation runs in O(log n) time.
  pub fn top_swap(&mut self, key:KT, val:VT) -> Option<(KT,VT)> {
    if self.vals.len()==0 {
      self.push(key,val);
      return None;
    }
    let (h,exists) = self.findslot(&key);
    if exists {  // replace key,val then pop
      let (ki,vi) = *self.kmap.get(&h).unwrap();
      self.keys[ki] = Some(key);
      self.vals[vi] = (val,h);
      self.reposition(vi);
      return self.pop();
    }
    // get info about top value
    let (_,it) = &self.vals[0];
    let (tki,tvi) = *self.kmap.get(it).unwrap();
    assert!(tvi==0);
    let mut newkey = Some(key);
    let mut newval = (val,h);
    core::mem::swap(&mut newkey, &mut self.keys[tki]);
    core::mem::swap(&mut newval, &mut self.vals[0]);
    self.kmap.insert(h, (tki,0));
    self.swapdown(0);
    Some((newkey.unwrap(), newval.0))
  }//swap

  /// Returns the key-value pair with the highest priority value (smallest
  /// or largest depending on minheap or maxheap).  This operation runs in
  /// O(1) time
  pub fn peek(&self) -> Option<(&KT,&VT)> {
    if self.vals.len()==0 {return None;}
    let (v,hv) = &self.vals[0];
    let k = self.kmap.get(hv).unwrap().0;
    Some((self.keys[k].as_ref().unwrap(),v))
  }//peek

  /// Removes and returns the key-value pair with highest priority value
  /// (smallest or largest depending on minheap or maxheap).  This operation
  /// runs in O(log n) time
  pub fn pop(&mut self) -> Option<(KT,VT)> {
    let vn = self.vals.len();
    if vn==0 {return None;}
    self.heapswap(0,vn-1);
    let mut Kopt = None;
    let (V,iv) = self.vals.pop().unwrap();
    let (ki,vi) = *self.kmap.get(&iv).unwrap();
    core::mem::swap(&mut self.keys[ki], &mut Kopt);
    // entry persist in kmap for rehashing
    self.swapdown(0);
    Some((Kopt.unwrap(),V))
  }//pop

  /// returns the value associated with the given key, if it exists.  
  /// Indexed access is also available, but will panic if the key is not found.
  /// This operation runs in O(1) time.
  ///
  /// Note that **there is no `get_mut` operation** as mutations will
  /// require values to be repositioned in the heap.  Call instead the
  /// [HashHeap::modify] operation.
  pub fn get(&self, key:&KT) -> Option<&VT> {  //O(1)
    if let (h,true) = self.findslot(key) {
      let (_,vi) = self.kmap[&h];
      Some(&self.vals[vi].0)
    }
    else {None}
  }//get

  /// This operation applies the mutating closure to the value associated
  /// with the key, if it exists.  It then adjusts the position of the
  /// value inside the heap.  It returns true on success and false if
  /// the key was not found. This operation runs in O(log n) time assuming
  /// minimal cost for calling the closure.  
  pub fn modify<F>(&mut self, key:&KT, mapfun:F) -> bool
      where F : FnOnce(&mut VT)
  {
    if let (h,true) = self.findslot(key) {
      let (_,vi) = self.kmap[&h];
      mapfun(&mut self.vals[vi].0);
      self.reposition(vi);
      true
    }
    else {false}
  }//modify

  /// Removes and returns the key-value pair with the given key reference, if it
  /// exists.  This operation runs in O(log n) time.
  pub fn remove(&mut self, key:&KT) -> Option<(KT,VT)> {
    if let (h,true) = self.findslot(key) {
      let (ki,vi) = self.kmap[&h];
      self.heapswap(vi,self.vals.len()-1);
      let (V,_) = self.vals.pop().unwrap();
      //if vi < self.vals.len() {self.reposition(vi);}  //vi was not popped
      self.reposition(vi);
      let mut K = None;
      core::mem::swap(&mut K, &mut self.keys[ki]);
      Some((K.unwrap(),V))
    }
    else {None}  
  }//remove

  /// Determines if the given key exists in the HashHeap. This is an
  /// O(1) operation.
  pub fn contains_key(&self, key:&KT) -> bool {   // O(1)
    self.findslot(key).1
  }

  /// Determines if the given value exists in the table.  This operation
  /// **runs in O(n) time**.
  pub fn contains_val(&self,val:&VT) -> bool {  // O(n)
    self.valsearch(0,val)
  }
  fn valsearch(&self, root:usize, val:&VT) -> bool {
    if root >= self.vals.len() {false}
    else if &self.vals[root].0 == val {true}
    else if (self.lessthan)(&self.vals[root].0,val) {false}
    else {self.valsearch(left(root),val) || self.valsearch(right(root),val)}
  }

  // treat as maxheap 
  fn swapup(&mut self, mut i:usize) -> usize {
    if i>=self.vals.len() {return i;}
    let mut p = parent(i);
    while i>0 && (self.lessthan)(&self.vals[p].0 , &self.vals[i].0) {
       self.heapswap(i,p);
       i = p;
       p = parent(i);
    }//while
    i
  }//swapup returns final position of ith val

  fn swapdown(&mut self, mut i:usize) -> usize {
    let size = self.vals.len();
    let nonleaves = size - ((size+1)/2);
    let mut sc = 0;
    while (i<nonleaves && sc != usize::MAX) {  // refine
       sc = usize::MAX;
       let li = left(i);
       let ri = right(i);
       if li<size && (self.lessthan)(&self.vals[i].0 , &self.vals[li].0) {
         sc = li;
       }
       if ri<size && (self.lessthan)(&self.vals[i].0 , &self.vals[ri].0)
          && (self.lessthan)(&self.vals[li].0 , &self.vals[ri].0) { sc = ri; }
       if (sc != usize::MAX) { //swap
         self.heapswap(i,sc);
         i = sc;
       }
    }//while
    i
  }//swapdown

  fn reposition(&mut self, i:usize) -> usize {
     let mut ni = self.swapup(i);
     if ni==i {ni=self.swapdown(i);}
     ni
  }//reposition

  // swap values at indices i, j in vals, re-associate
  fn heapswap(&mut self, i:usize, j:usize) {
    if i==j {return;}
    let ih = self.vals[i].1;   //hash-index of corresponding key
    let jh = self.vals[j].1;  
    self.vals.swap(i,j);
    self.kmap.get_mut(&ih).map(|(_,vi)|{*vi=j;});
    self.kmap.get_mut(&jh).map(|(_,vj)|{*vj=i;});
    // hash-index does not change- need for future lookup
  }// swap values in vals, re-associate

  fn heapify(&mut self, vkv:Vec<(KT,VT)>) {
    if self.keys.len()>0 {
      self.keys.clear();
      self.vals.clear();
      self.kmap.clear();
    }
    let vn = vkv.len();
    let nonleafs = vn - (vn+1)/2;
    let mut vi = 0;
    for (k,v) in vkv {
      let (kh,_) = self.findslot(&k);
      self.keys.push(Some(k));
      self.vals.push((v,kh));
      self.kmap.insert(kh,(vi,vi));
      vi += 1;
    }//for
    vi = nonleafs;
    while vi>0 {  // heapify loop
      self.swapdown(vi-1);
      vi -= 1;
    }//while
  }//heapify

  /// returns the number of key-value pairs in the HashHeap in constant time.
  pub fn len(&self)->usize { self.vals.len() }

  /// reserves additional capacity
  pub fn reserve(&mut self, additional:usize) {
    self.kmap.reserve(additional);
    self.vals.reserve(additional);
    self.keys.reserve(additional);    
  }//reserve

  /// clears HashHeap without changing capacity.  Also resets [RandomState]
  /// for hasher.
  pub fn clear(&mut self) {
    self.vals.clear();
    self.keys.clear();
    self.kmap.clear();
    self.autostate.replace(RandomState::new());
  }//clear

  /// returns true if the structure is a max-hashheap and false if it's a
  /// min-hashheap.
  pub fn is_max_hashheap(&self) -> bool {self.minmax}

  /*
  pub fn diagnostic(&self) {
    if self.tc>0 {println!("total collisions: {}",self.tc);}
  }
  */
}// impl HashHeap

//default
impl<KT:Hash+Eq, VT:Ord> Default for HashHeap<KT,VT> {
  fn default() -> Self {
     Self::new_maxheap()
  }
} // impl default

use core::fmt::Debug;
impl<KT:Hash+Eq+Debug, VT:Ord+Debug> Debug for HashHeap<KT,VT> {
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let mut fp = f.pad("HashHeap: [\n");
        let width = 14;
        for (key,val) in self.iter() {
          fp = f.pad(&format!("  key {:?}  :  value {:?}\n",key,val));
        }
        fp = f.pad("]\n");
        fp
    }
} // impl default


impl<KT:Hash+Eq+Clone, VT:Ord+Clone> Clone for HashHeap<KT,VT> {
  fn clone(&self) -> Self {
    HashHeap {
      keys : self.keys.clone(),
      vals : self.vals.clone(),
      userhash : self.userhash.clone(),
      rehash : self.rehash.clone(),
      kmap : self.kmap.clone(),
      lessthan : self.lessthan.clone(),
      autostate : RefCell::new(RandomState::new()),
      minmax : self.minmax,
    }
  }//clone
} // impl clone





/// indexed get
impl<KT:Hash+Eq,VT:Ord> core::ops::Index<&KT> for HashHeap<KT,VT>
{
  type Output = VT;
  fn index(&self, index:&KT)-> &Self::Output
  {
     self.get(index).expect("key not found")
  }
}//impl Index

/// The implementation of this `From` trait always returns a max-hashheap.
/// For a min-hashheap, call instead [HashHeap::from_pairs]
impl<KT:Hash+Eq,VT:Ord> From<Vec<(KT,VT)>> for HashHeap<KT,VT>
{
  fn from(v:Vec<(KT,VT)>) -> HashHeap<KT,VT> {
    HashHeap::from_pairs(v,true)
  }
}

/// The implementation of this `From` trait always returns a min-hashheap.
/// For a max-hashheap, call [Iterator::collect] followed by [HashHeap::from_pairs]
impl<KT:Hash+Eq,VT:Ord> FromIterator<(KT,VT)> for HashHeap<KT,VT>
{
  fn from_iter<T:IntoIterator<Item=(KT,VT)>>(iter:T) -> HashHeap<KT,VT> {
    HashHeap::from_pairs(iter.into_iter().collect(),false)
  }
}



////// iterator implementations

/// This iterator is returned by the [HashHeap::keys] function
pub struct KeyIter<'a,KT> {
   keys : &'a [Option<KT>],
   index : usize
}
impl<'a,KT> Iterator for KeyIter<'a,KT> {
  type Item = &'a KT;
  fn next(&mut self) -> Option<Self::Item> {
    let kn = self.keys.len();
    while self.index<kn && self.keys[self.index].is_none() {
      self.index+=1;
    }
    if self.index >= kn {None}
    else {
      self.index+=1;
      self.keys[self.index-1].as_ref()
    }
  }//next
}// keys iterator

/// This iterator is returned by the [HashHeap::values] function
pub struct ValIter<'a,VT> {
   vals : &'a [(VT,usize)],
   index : usize,
}
impl<'a,VT> Iterator for ValIter<'a,VT> {
  type Item = &'a VT;
  fn next(&mut self) -> Option<Self::Item> {
    let vn = self.vals.len();
    if self.index >= vn {None}
    else {
      self.index += 1;
      Some(&self.vals[self.index-1].0)
    }
  }//next
}// vals iterator

/// This iterator is returned by the [HashHeap::iter] function
pub struct KeyValIter<'a,KT,VT> {
  hh: &'a HashHeap<KT,VT>,
  index : usize,
}
impl<'a,KT:Hash+Eq,VT:Ord> Iterator for KeyValIter<'a,KT,VT> {
  type Item = (&'a KT, &'a VT);
  fn next(&mut self) -> Option<Self::Item> {
    let vn = self.hh.vals.len();
    while self.index<vn
    {
      let (v,iv) = &self.hh.vals[self.index];
      self.index += 1;
      let (ki,_) = self.hh.kmap[iv];
      if let Some(k) = &self.hh.keys[ki] {return Some((k,v));}
    }
    None
  }//next
}// key-val iterator


impl<'a,KT:Hash+Eq, VT:Ord> HashHeap<KT,VT>
{
  /// returns an iterator over the keys of the structure in no particular
  /// order
  pub fn keys(&'a self) -> KeyIter<'a,KT> {
    KeyIter {
      keys: &self.keys,
      index:0,
    }
  }//keys

  /// returns an iterator over the values of the structure in no particular
  /// order
  pub fn values(&'a self) -> ValIter<'a,VT> {
    ValIter {
      vals: &self.vals,
      index: 0,
    }
  }//values

  /// returns an iterator over `(key,value)` pairs of the structure
  /// in no particular order.
  ///
  /// Note that, because of the need to swap values up or down the
  /// heap after a mutation, there is no `iter_mut` available.  Use the
  /// [HashHeap::modify] operation to mutate single values instead.
  pub fn iter(&'a self) -> KeyValIter<'a,KT,VT> {
    KeyValIter {
      hh: self,
      index:0,
    }
  }
}// impl iterators

/// The IntoIterator for references is the same as calling [HashHeap::iter],
/// and will therefore return references in **arbitrary order**.
impl<'t,KT:Hash+Eq,VT:Ord> IntoIterator for &'t HashHeap<KT,VT> {
    type Item = (&'t KT,&'t VT);
    type IntoIter = KeyValIter<'t,KT,VT>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}//IntoIter for references

/// Consuming iterator, type for [IntoIterator].  This iterator will
/// call [HashHeap::pop] for the next (key,value) pair, and will thus
/// return the values in **sorted order** (increasing for min-hashheap,
/// decreasing for max-hashheap).
pub struct IntoIter<KT,VT>(HashHeap<KT,VT>);
impl<KT:Hash+Eq,VT:Ord> Iterator for IntoIter<KT,VT> {
  type Item = (KT,VT);
  fn next(&mut self) -> Option<(KT,VT)> {
    self.0.pop()
  }
}//impl IntoIter

/// The consuming iterator is implemented by [IntoIter] and will return
/// the owned values in **sorted order** 
impl<KT:Hash+Eq,VT:Ord> IntoIterator for HashHeap<KT,VT> {
    type Item = (KT,VT);
    type IntoIter = IntoIter<KT,VT>;

    fn into_iter(self) -> Self::IntoIter {
       IntoIter(self)
    }
}// consuming iterator


//////////testing
#[cfg(test)]
mod tests {
  use super::*;
  #[test]
  fn it_works() {
    let mut priority_map = HashHeap::<&str,u32>::new_minheap();
    priority_map.insert("A", 4);   // O(1) average, O(log n) worst
    priority_map.insert("B", 2);
    priority_map.insert("C", 1);
    priority_map.insert("D", 3);
    priority_map.insert("E", 4);
    priority_map.insert("F", 5);
    priority_map.insert("A", 6);   // insert can also modify
    // iterator tests:
    let mut total = 0;
    for (key,val) in &priority_map {
      println!("iterator key {} : val {}",key,val);
      total += val;
    }
    assert_eq!(total,21);

    for (key,val) in priority_map {
      println!("consuming iterator key {} : val {}",key,val);
    }
  }//it_works
}//tests module
