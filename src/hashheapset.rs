//! This module contains the implementation of a ***Hash Heap Set***, where
//! values in the set must implement Hash, Eq and PartialOrd.  It uses 
//! two vectors underneath.  The first vector contains entries of the form
//! (Option) (value, vi) where vi is an index in the second vector.  The
//! second vector contains indices of the first vector that points to it.
//! The first vector is implemented as a linear probing hashmap and the
//! second vector is implemented has a heap.

#![allow(dead_code)]
#![allow(unused_variables)]
#![allow(non_snake_case)]
#![allow(non_camel_case_types)]
#![allow(unused_parens)]
#![allow(unused_mut)]
#![allow(unused_assignments)]
#![allow(unused_doc_comments)]
#![allow(unused_imports)]
use core::cmp::Ord;
use core::fmt::{Display,Debug};
use std::collections::hash_map::RandomState;
use core::hash::{BuildHasher, Hash, Hasher};
use core::convert::From;

//global heap calculations
fn left(i:usize) -> usize { 2*i+1 }
fn right(i:usize) -> usize { 2*i+2 }
fn parent(i:usize) -> usize { (i-1)/2 }

fn optcmp<VT:PartialOrd>(a:&Option<(VT,usize)>, b:&Option<(VT,usize)>, neg:bool) -> bool
{
  match (a,b,neg) {
    (Some((av,_)), Some((bv,_)),true) => av < bv,
    (Some((av,_)), Some((bv,_)),false) => bv < av,
    _ => false,
  }
}

/// A HashHeapSet data structure that requires values to be ordered as well
/// as hashable.
#[derive(Clone,Debug)]
pub struct HashHeapSet<T> {
  table : Vec<Option<(T,usize)>>,
  heap: Vec<usize>,
  maxhashes : Vec<usize>,
  maxheap : bool,
  mask : usize,
  autostate : RandomState,
}

impl<T:Hash+Eq+PartialOrd> HashHeapSet<T> {

  fn with_cap(cap:usize, ismax:bool) -> Self {
    let mut tab = Vec::with_capacity(cap);
    let mut hp = Vec::with_capacity(cap);
    let mut mh = Vec::with_capacity(cap);
    tab.resize_with(cap,||None);
    mh.resize(cap,0);
    HashHeapSet {
      table : tab,
      heap : hp,
      maxhashes : mh,
      maxheap : ismax,
      mask : cap - 1,
      autostate: RandomState::new(),
    }
  } // with_cap

  /// creates a HashHeapSet with requested capacity, with boolean indicating
  /// max- or min-heap (true means maxheap). The actual capacity will be
  /// the closest power of 2 that's greater than or equal to the requested
  /// capacity.
  pub fn with_capacity(requested_cap:usize, ismax:bool) -> Self {
    let mut cap = 1;
    while cap < requested_cap { cap *= 2; }
    Self::with_cap(cap,ismax)
  }

  /// conveniently creates a new maxheap with an initial capacity of 16
  pub fn new_maxheap() -> Self {
    Self::with_capacity(16,true)
  }
  /// conveniently creates a new minheap with an initial capacity of 16  
  pub fn new_minheap() -> Self {
    Self::with_capacity(16,false)
  }

  /// converts a vector into a heap using the heapify algorithm, skips
  /// duplicates.  ismax=true indicates maxheap.
  pub fn from(mut v:Vec<T>, ismax:bool) -> Self {
    let mut set = Self::with_capacity(v.len()*2,ismax);
    let mut vi = 0;
    while let Some(x) = v.pop() {
      let h0 = set.hash(&x);
      let mut h = h0;
      let mut hashes = 1;
      loop {
        match &set.table[h] {
          Some((w,_)) if &x==w => {break;},
          Some(_) => {
            h = (h+1) & set.mask;
            hashes += 1;
          },
          None => {
            set.heap.push(h);
            set.table[h] = Some((x,vi));
            vi += 1;
            break;
          },
        }
      }//loop
      if hashes > set.maxhashes[h0] { set.maxhashes[h0]=hashes; }
    }//while let
    let vn = set.heap.len();
    let nonleafs = vn - (vn+1)/2;
    let mut vi = nonleafs;
    while vi>0 {
      set.swapdown(vi-1);
      vi -= 1;
    }
    set
  }//from
  
  /// returns the number of entries in the set
  pub fn len(&self) -> usize { self.heap.len() }
  /// returns the current capacity
  pub fn current_capacity(&self) -> usize { self.mask+1 }
  /// returns whether the current set is a maxheap (if true) or minheap (if false)
  pub fn is_maxheap(&self) -> bool { self.maxheap }

  fn lessthan(&self,a:&Option<(T,usize)>,b:&Option<(T,usize)>) -> bool {
    optcmp(a,b,self.maxheap)
  }

  fn hash(&self,key:&T) -> usize {
     let mut bs = self.autostate.build_hasher();
     key.hash(&mut bs);
     (bs.finish() as usize) & self.mask
  }
  
  fn swap(&mut self, i:usize, k:usize) {
    self.heap.swap(i,k);
    let ik = self.heap[i];
    self.table[ik].as_mut().map(|pair|pair.1 = i);
    let kk = self.heap[k];
    self.table[kk].as_mut().map(|pair|pair.1 = k);
  }

  fn swapup(&mut self, mut i:usize) -> usize {
    let mut pi = if i>0 {parent(i)} else {0};
    let mut hi = self.heap[i];
    let mut hpi = self.heap[pi];
    while i>0 && self.lessthan(&self.table[hpi],&self.table[hi]) {
      //println!("swap {} with {}",i,pi);
      self.swap(i,pi);
      i = pi;
      if i>0 { pi = parent(i); }
      hi = self.heap[i];
      hpi = self.heap[pi];      
    }
    i
  }//swapup

  fn swapdown(&mut self, mut i:usize) -> usize {
    let mut si = Some(0);
    while let Some(_) = si {
      si = None;
      let lf = left(i);
      let rt = right(i);
      let hi = self.heap[i];
      if lf<self.heap.len() {
        let hlf = self.heap[lf];
        if self.lessthan(&self.table[hi],&self.table[hlf]) {
          si = Some(lf);
        }
        if rt<self.heap.len() {
          let hrt = self.heap[rt];
          if self.lessthan(&self.table[hi],&self.table[hrt])
             && self.lessthan(&self.table[hlf],&self.table[hrt]) {
             si = Some(rt);
          }
        }
      }
      if let Some(k) = si {
        self.swap(i,k);
        i = k;
      }
    }//while
    i
  }//swapdown


  fn adjust(&mut self, i:usize, both:bool) -> usize {
    let k = self.swapup(i);
    if k==i && both {self.swapdown(i)} else {k}
  }

  fn resize(&mut self, newcap:usize) -> bool {
    if self.heap.len() > newcap { return false; }
    let mut newmap = Self::with_cap(newcap, self.maxheap);
    for h in &self.heap {
      let mut temp = None;
      core::mem::swap(&mut temp, &mut self.table[*h]);
      temp.map(|(w,_)|newmap.add(w));
    }
    core::mem::swap(self,&mut newmap);
    true
  }

  /// doubles the capacity of the set.  This function is automatically
  /// called when the load factor (size/capapcity) becomes greater than .75.
  pub fn doublesize(&mut self) {
    self.resize(self.table.len()*2);
  }

  /// halfs the capacity of the set, returns false without resizing if
  /// the resulting capacity is less than the current size.
  pub fn halfsize(&mut self) -> bool {
    self.resize(self.table.len()/2)
  }

  fn add(&mut self, v:T) {
    let h0 = self.hash(&v);
    let mut h = h0;
    let mut hashes = 1;
    loop {
      match &self.table[h] {
        Some(_) => {
          h = (h+1) & self.mask;
          hashes += 1;
        },
        None => {
          break;
        },
      }
    }//loop
    if hashes > self.maxhashes[h0] { self.maxhashes[h0] = hashes; }
    self.heap.push(h);
    self.table[h] = Some((v,self.heap.len()-1));
    self.swapup(self.heap.len()-1);
  }

  fn findslot(&mut self, v:&T) -> Option<usize> {
    let h0 = self.hash(v);
    let mut h = h0;
    let mut hashes = 1;
    let mut reuse_index = None;
    loop {
      match &self.table[h] {
        Some((w,wi)) if v==w => {
          return None;
        },
        Some(_) => {
          h = (h+1) & self.mask; 
          hashes += 1;
        },
        None if hashes<self.maxhashes[h0] => {
          if let None = reuse_index { reuse_index = Some(h); }
          h = (h+1) & self.mask;
          hashes += 1;          
        },
        None => {
          break;
        },
      }//match
    }//loop
    if hashes > self.maxhashes[h0] { self.maxhashes[h0] = hashes; }
    if let Some(r) = reuse_index { h = r; }
    Some(h)
  }

  /// inserts new value into the set, returns false if value already exists.
  pub fn insert(&mut self, v:T) -> bool
  {
    if self.heap.len()*100 > self.table.len()*75 {
      self.resize(self.table.len()*2);
    }
    if let Some(h) = self.findslot(&v) {
      self.heap.push(h);
      self.table[h] = Some((v,self.heap.len()-1));
      self.swapup(self.heap.len()-1);
      true
    }
    else { false }
  } // insert

  /// alias for insert
  pub fn push(&mut self, v:T) -> bool {
    self.insert(v)
  }

  fn findkey(&self, v:&T) -> Option<usize> {
    let h0 = self.hash(&v);
    let mut h = h0;
    let mut hashes = 1;
    loop {
      match &self.table[h] {
        Some((w,wi)) if v==w => { return Some(h); },
        _ if hashes<self.maxhashes[h0] => {
          h = (h+1) & self.mask;
          hashes += 1;
        },
        _ => { break; }
      }//match
    }//loop
    None
  }

  /// determines if a value is present in the set
  pub fn contains(&self, v:&T) -> bool {
    match self.findkey(v) {
      Some(h) => true,
      _ => false,
    }
  }

  /// removes a value from the set, returns false if value not found
  pub fn remove(&mut self,v:&T) -> bool {
    match self.findkey(v) {
      Some(h) => {
        let mut temp = None;
        core::mem::swap(&mut temp, &mut self.table[h]);
        if let Some((w,wi)) = temp {
          if self.heap.len()>1 {
            self.swap(wi, self.heap.len()-1);
            self.heap.pop();
            self.adjust(wi, wi<self.heap.len());
          }
          else { self.heap.pop(); }
        }
        true
      },
      None => false,
    }
  }

  /// removes and returns highest priority value
  pub fn pop(&mut self) -> Option<T> {
    if self.heap.len()<1 { return None; }
    let h = self.heap[0];
    let mut temp = None;
    core::mem::swap(&mut temp, &mut self.table[h]);
    if self.heap.len()>1 {
      self.swap(0,self.heap.len()-1);
      self.heap.pop();      
      self.swapdown(0);
    }
    else { self.heap.pop(); }
    temp.map(|p|p.0)
  }

  /// returns reference to highest priority value without removal
  pub fn peek(&self) -> Option<&T> {
    if self.heap.len()<1 { return None; }
    let h = self.heap[0];
    self.table[h].as_ref().map(|(v,_)|v)
  }

  /// creates an immutable iterator over the set.  The values will be
  /// iterated in the order in which they appear in the heap.  The first
  /// value iterated will be of the highest priority.
  pub fn iter<'t>(&'t self) -> HHSIter<'t,T> {
    HHSIter {
      hs : self,
      i : 0,
    }
  }

  /// creates a mutable priority stream iterator, which calls .pop on
  /// each iteration
  pub fn priority_stream<'t>(&'t mut self) -> PrioritySetIter<'t,T> {
    PrioritySetIter(self)
  }
}// impl HashHeapSet

impl<T:Display> HashHeapSet<T> {
  /// for diagnostic information concerning underlining structure
  pub fn diagnostic(&self) {
    /*
    for h in 0 .. self.table.len() {
      if let Some((w,wi)) = &self.table[h] {
        println!("{} : {}, heap {}",h,w,wi);
      }
    }
    */
    for i in 0 .. self.heap.len() {
      let h = self.heap[i];
      if let Some((w,wi)) = &self.table[h] {
        println!("heap {}, hash index {}, val {}, maxhashes {}",i,h,w,self.maxhashes[h]);
      }
    }
  }
}

/// Structure returned by [HashHeapSet::iter]
pub struct HHSIter<'t,T> {
  hs : &'t HashHeapSet<T>,
  i : usize,
}

impl<'t,T> Iterator for HHSIter<'t,T> {
  type Item = &'t T;
  fn next(&mut self) -> Option<Self::Item> {
    if self.i >= self.hs.heap.len() { return None; }
    let h = self.hs.heap[self.i];
    match &self.hs.table[h] {
      Some((w,wi)) => {
        self.i += 1;
        Some(w)
      },
      _ => None,
    }
  }
}

impl<'t,T:Hash+Eq+PartialOrd> IntoIterator for &'t HashHeapSet<T> {
  type Item = &'t T;
  type IntoIter = HHSIter<'t,T>;
  fn into_iter(self) -> Self::IntoIter {
    self.iter()
  }
}

/// Structure returned by [HashHeapSet::priority_stream]
pub struct PrioritySetIter<'t,T>(&'t mut HashHeapSet<T>);

impl<'t,T:Hash+Eq+PartialOrd> Iterator for PrioritySetIter<'t,T> {
  type Item = T;
  fn next(&mut self) -> Option<Self::Item> {
    self.0.pop()
  }
}

impl<'t,T:Hash+Eq+PartialOrd> IntoIterator for &'t mut HashHeapSet<T> {
  type Item = T;
  type IntoIter = PrioritySetIter<'t,T>;
  fn into_iter(self) -> Self::IntoIter {
    self.priority_stream()
  }
}
