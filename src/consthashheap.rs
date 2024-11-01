//! This module contains a new implementation of the hashed heap structure,
//! [ConstHashHeap]. The main external difference is that the capacity
//! of the structure must be known at compile time.
//! However, a [ConstHashHeap::resize] function is provided to transfer
//! entries to a structure of higher capacity.  There are also many
//! internal changes that should improve performance.  Rust HashMaps are
//! no longer employed anywhere.  Instead, each ConstHashHeap contains
//! two arrays, keys and values.  The keys array contains (Option) entries of
//! form (key,vi) where vi is the index in the values array that contains
//! the mapped value.  The values array contains entries of the form
//! (value,ki) where ki is the index in the keys array of the corresponding
//! key.  The keys array is treated as a closed hashmap (open addressing)
//! with a linear probing rehash function.  The values array is treated
//! as a binary heap. Swapping values in the values array updates
//! the corresponding information in the keys array using the ki index
//! which it possesses.  The ki index does not change until the entire
//! structure is resized.


#![allow(dead_code)]
#![allow(unused_variables)]
#![allow(non_snake_case)]
#![allow(non_camel_case_types)]
#![allow(unused_parens)]
#![allow(unused_mut)]
#![allow(unused_assignments)]
#![allow(unused_doc_comments)]
#![allow(unused_imports)]
use core::cell::{Ref, RefCell, RefMut};
use core::cmp::Ord;
use core::fmt::{Display,Debug};
use std::collections::hash_map::RandomState;
use core::hash::{BuildHasher, Hash, Hasher};


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

/// The default capacity of a ConstHashHeap is 1024.  Exact powers of
/// two are recommended for other capacities.  Resizing is recommended
/// when the [ConstHashHeap::load_factor] function returns a value greater 
/// than 0.75.  
#[derive(Clone, Debug)]
pub struct ConstHashHeap<KT,VT, const CAPACITY:usize = 1024>
{
   keys : [Option<(KT,usize)>;CAPACITY],
   vals : [Option<(VT,usize)>;CAPACITY],
   maxhashes : [usize;CAPACITY], // max number of hashes from start
   size : usize,
   autostate: RefCell<RandomState>,
   lessthan : fn(&Option<(VT,usize)>,&Option<(VT,usize)>) -> bool,
}
impl<KT:Hash+Eq, VT:PartialOrd, const CAP:usize> ConstHashHeap<KT,VT,CAP> {

  /// creates a new ConstHashHeap.  The boolean argument distinguishes
  /// maxheap and minheap, true = maxheap.
  pub fn new(maxheap:bool) -> Self {
    ConstHashHeap {
      keys : [const { None }; CAP],
      vals : std::array::from_fn(|_|None),
      maxhashes : [0;CAP],
      size : 0,
      autostate : RefCell::new(RandomState::new()),
      lessthan : if maxheap{|a,b|optcmp(a,b,true)} else {|a,b|optcmp(a,b,false)},
    }
  }
  
  fn hash(&self,key:&KT) -> usize {
     let mut rs = &mut *self.autostate.borrow_mut();
     let mut bs = rs.build_hasher();
     key.hash(&mut bs);
     (bs.finish() as usize) % CAP
  }

  fn rehash(h:usize) -> usize { (h+1) % CAP }

  fn swap(&mut self, i:usize, k:usize) {
    self.vals.swap(i,k);
    if let Some((ival,ik)) = &mut self.vals[i] {
         self.keys[*ik].as_mut().map(|pair|pair.1 = i);
    }
    if let Some((kval,kk)) = &mut self.vals[k] {
         self.keys[*kk].as_mut().map(|pair|{pair.1 = k;});
    }    
  }//swap

  fn swapup(&mut self, mut i:usize) -> usize {
    let mut pi = if (i>0) {parent(i)} else {0};
    while (i>0 && (self.lessthan)(&self.vals[pi],&self.vals[i])) {
       self.swap(i,pi);
       i = pi;
       if (i>0) {pi = parent(i)};
    }
    i
  }//swapup

  fn swapdown(&mut self, mut i:usize) -> usize {
    let mut si = Some(0);
    while si.is_some() {
      si = None;
      let lf = left(i);
      let rt = right(i);
      //println!("{i}: left {lf}, right {rt}");
      //println!("test: {}",(self.lessthan)(&self.vals[i],&self.vals[lf]));
      if (lf<self.size && (self.lessthan)(&self.vals[i],&self.vals[lf])) {
        si = Some(lf);
      }
      if(rt<self.size && (self.lessthan)(&self.vals[i],&self.vals[rt])
         && (self.lessthan)(&self.vals[lf],&self.vals[rt])) {
        si = Some(rt);
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

  /// The number of key-value pairs stored in the structure
  pub fn size(&self) -> usize {self.size}

  /// Either inserts a new key-value pair into the structure,
  /// or if a duplicate key already exists, change the value
  /// associated with the key.  As in a hashmap, keys must be
  /// unique.  true is returned on successful insertion and
  /// false is returned only if capacity has been reached.
  /// This operation takes O(log n) time.
  pub fn insert(&mut self, key:KT, val:VT) -> bool
  { 
    //if (self.size >= CAP) {return false;}
    let h0 = self.hash(&key);
    let mut h = h0;
    let mut hashes = 1;
    let mut target_index = -1;
    let mut keyfoundloc = None;
    loop {
      match &self.keys[h] {
        Some((k,vi)) if k==&key => {
          keyfoundloc = Some(*vi);
          break;
        },
        Some(_) => { h = Self::rehash(h); hashes+=1; },
        None if hashes <= self.maxhashes[h0] => {
          if target_index == -1 { target_index = h as isize; }
          h=Self::rehash(h);
          hashes += 1;
        },
        None => {
          //self.keys[h] = Some((key,self.size-1));
          // push Some((val,h)) on heap, get location
          keyfoundloc = Some(self.size);
          break;
        },
      }//match
    }// loop
    match &keyfoundloc {  // reuse slot
      Some(vi) if *vi==self.size && self.size >= CAP => {
        return false;
      }
      Some(vi) if *vi == self.size => {
        self.size+=1;
        if target_index>=0 {h = target_index as usize;}
      },
      _ => {},
    }//match
    if hashes > self.maxhashes[h0] {
      self.maxhashes[h0] = hashes;
    }
    if let Some(vi) = keyfoundloc {
        self.keys[h] = Some((key,vi));
        self.vals[vi] = Some((val,h));
        self.adjust(vi, vi+1<self.size);
    }
    true
  }//set

  /// alias for [Self::insert]
  pub fn push(&mut self, key:KT, val:VT) -> bool {  // alias for insert
     self.insert(key,val)
  }

  /// returns reference to value associated with key, if it exists.
  /// This operation is also called in the implementation of the [core::ops::Index]
  /// trait. This is an O(log n) operation.
  pub fn get(&self, key:&KT) -> Option<&VT> {
    let mut answer = None;
    let h0 = self.hash(&key);
    let mut h = h0;
    let mut hashes = 1;
    loop {
      match &self.keys[h] {
        Some((k,vi)) if k==key => {
          answer = self.vals[*vi].as_ref().map(|p|&p.0);
          break;
        },
        Some(_) => {
          h=Self::rehash(h);
          hashes += 1;
        },
        None if hashes <= self.maxhashes[h0] => {
          h=Self::rehash(h);
          hashes += 1;        
        }
        None => { break; }
      }//match
    }//loop
    answer
  }//get

  /// modifies the entry associated with the key, if it exists, using
  /// the provided closure.  This procedure will adjust the position of
  /// of the entry in the priority heap after modification. This
  /// operation is O(log n) plus the cost of calling the closure.
  pub fn modify<F:FnOnce(&mut VT)>(&mut self, key:&KT, f:F) -> bool {
    let h0 = self.hash(&key);
    let mut h = h0;
    let mut hashes = 1;
    let mut keyfoundloc = None;
    loop {
      match &self.keys[h] {
        Some((k,vi)) if k==key => {
          keyfoundloc = Some(*vi);
          break;
        },
        Some(_) => {
          h=Self::rehash(h);
          hashes += 1;
        },
        None if hashes <= self.maxhashes[h0] => {
          h=Self::rehash(h);
          hashes += 1;        
        }
        None => { break; }
      }//match
    }//loop
    if let Some(vi) = keyfoundloc {
      self.vals[vi].as_mut().map(|p|f(&mut p.0));
      self.adjust(vi, vi+1<self.size);
      true
    }
    else {false}
  }// modify

  /// remove and return the key-value pair associated with the key.
  /// O(log n)
  pub fn remove(&mut self, key:&KT) -> Option<(KT,VT)> {
    let mut answer = None;
    let mut keyfoundloc = None;    
    let h0 = self.hash(&key);
    let mut h = h0;
    let mut hashes = 1;
    loop {
      match &self.keys[h] {
        Some((k,vi)) if k==key => {
          keyfoundloc = Some(*vi);
          break;
        },
        Some(_) => {
          h=Self::rehash(h);
          hashes += 1;
        },
        None if hashes <= self.maxhashes[h0] => {
          h=Self::rehash(h);
          hashes += 1;        
        }
        None => { break; }
      }//match
    }//loop
    if let Some(vi) = keyfoundloc {
       let mut ak = None;
       let mut av = None;
       core::mem::swap(&mut ak, &mut self.keys[h]);
       core::mem::swap(&mut av, &mut self.vals[vi]);
       answer = ak.zip(av).map(|(a,b)|(a.0,b.0));
       // adjust heap;
       if (vi+1 != self.size) {
          self.swap(vi,self.size-1);
          self.adjust(vi,true);
       }
       self.size -= 1; 
    }
    answer
  }//remove

  /// remove and return the highest-priority key-value pair
  pub fn pop(&mut self) -> Option<(KT,VT)> {
    let mut answer = None;
    if self.size < 1 { return answer; }
    if let Some((_,ki)) = &self.vals[0] {
       let mut ak = None;
       let mut av = None;
       core::mem::swap(&mut ak, &mut self.keys[*ki]);
       core::mem::swap(&mut av, &mut self.vals[0]);
       answer = ak.zip(av).map(|(a,b)|(a.0,b.0));
       self.size -= 1;
       if (self.size>0) {
            self.swap(0,self.size);
            self.swapdown(0);
       }
    }
    answer  
  }//pop

  /// returns reference to highest-priority key-value pair without
  /// removal.  This operation is O(1).
  pub fn peek(&self) -> Option<(&KT,&VT)> {
    if self.size < 1 { None }
    else {
      self.vals[0].as_ref().and_then(|vp|
        self.keys[vp.1].as_ref().map(|kp|(&kp.0,&vp.0)))
    }
  }//peek

  /// The load factor is the size divided by the capacity.  Resizing is
  /// recommended when this factor is greater than 0.75.
  pub fn load_factor(&self) -> f32 {
    (self.size as f32) / (CAP as f32)
  }

  /// moves all entries to a ConstHashHeap of a new capacity.
  pub fn resize<const NEWCAP:usize>(mut self) -> ConstHashHeap<KT,VT,NEWCAP> {
    let mut hp2 = ConstHashHeap::new(true);
    hp2.lessthan = self.lessthan;
    hp2.size = self.size;
    for i in 0..self.size {
      let mut h = 0;
      if let Some((_,ki)) = &self.vals[i] {
         self.keys[*ki].as_ref().map(|(key,vi)|{
           let h0 = hp2.hash(key);
           h = h0;
           let mut hashes = 1;
           loop {
             match hp2.keys[h] {
               Some(_) => {
                 h = (h+1) % NEWCAP;
                 hashes += 1;
               },
               None => {
                 break;
               },
             }//match
           }//loop
           hp2.maxhashes[h0] = hashes;
         });
         core::mem::swap(&mut hp2.keys[h],&mut self.keys[*ki]);
         self.vals[i].as_mut().map(|p|{p.1 = h;});
      } // if-let
      core::mem::swap(&mut hp2.vals[i], &mut self.vals[i]);      
    }//for
    hp2
  }//resize

  /// moves all entries to a new ConstHashHeap of the same capacity. This
  /// operation may be called after a large number of key-value pairs
  /// had been removed, which should improve hash lookup performance.
  pub fn refresh(mut self) -> Self {
    self.resize()
  }

  /// returns a non-consuming iterator over all entries in no particular
  /// order.
  pub fn iter<'a>(&'a self) -> CHHIter<'a,KT,VT,CAP> {
    CHHIter {
      chh : self,
      index : 0,
    }
  }//iter

  /// returns a consuming iterator over all entries in order of priority.
  /// This iterator is equivalent to repeatedly calling [Self::pop], and
  /// will empty the structure of all entries.
  pub fn priority_stream<'a>(&'a mut self) -> PriorityStream<'a,KT,VT,CAP> {
    PriorityStream(self)
  }
  
}// main impl

/// indexed get, unwraps
impl<KT: Hash + Eq, VT: PartialOrd, const CAP:usize> core::ops::Index<&KT>
for ConstHashHeap<KT,VT,CAP>
{
    type Output = VT;
    fn index(&self, index: &KT) -> &Self::Output {
        self.get(index).expect("key not found")
    }
} //impl Index

impl<KT:Display+Debug+Hash+Eq, VT:Display+Debug+PartialOrd, const CAP:usize> ConstHashHeap<KT,VT,CAP>
{
  /// for debugging
  pub fn diagnostics(&self) {
    for i in 0..CAP {
      println!("{i}: {:?}, \t {:?} \t hash {}",&self.keys[i],&self.vals[i],
       self.keys[i].as_ref().map(|p|self.hash(&p.0).to_string()).unwrap_or(String::new()));
    }
    println!("--- size {}, capacity {} ---",self.size,CAP);
  }//diagnostics
}//diagnostics


/////////////////// iterators

/// Iterator for the [ConstHashHeap::iter] function
pub struct CHHIter<'a, KT,VT, const CAP:usize>
{
  chh : &'a ConstHashHeap<KT,VT,CAP>,
  index : usize,
}//CKVIter
impl<'a,KT: Hash + Eq, VT: PartialOrd, const CAP:usize>
Iterator for CHHIter<'a,KT,VT,CAP> {
  type Item = (&'a KT, &'a VT);
  fn next(&mut self) -> Option<Self::Item> {
    let mut answer = None;
    if self.index >= self.chh.size() {return answer;}
    self.index+=1;
    if let Some((val,ki)) = &self.chh.vals[self.index-1] {
      if let Some((key,vi)) = &self.chh.keys[*ki] {
         answer = Some((key,val));
      }
    }
    answer
  }//next
}// CHHIter impl

impl<'a, KT: Hash + Eq, VT: PartialOrd, const CAP:usize> IntoIterator
for &'a ConstHashHeap<KT,VT,CAP>
{
  type Item = (&'a KT, &'a VT);
  type IntoIter = CHHIter<'a,KT,VT,CAP>;
  fn into_iter(self) -> Self::IntoIter {
    self.iter()
  }
}// ref intoiter

/// Iterator for the [ConstHashHeap::priority_stream] function
pub struct PriorityStream<'a,KT,VT,const CAP:usize>(&'a mut ConstHashHeap<KT,VT,CAP>);
impl<'a,KT: Hash + Eq, VT: PartialOrd, const CAP:usize> Iterator
for PriorityStream<'a,KT,VT,CAP>
{
  type Item = (KT,VT);
  fn next(&mut self) -> Option<Self::Item> {
    self.0.pop()
  }
}

impl<'a, KT: Hash + Eq, VT: PartialOrd, const CAP:usize> IntoIterator
for &'a mut ConstHashHeap<KT,VT,CAP>
{
  type Item = (KT,VT);
  type IntoIter = PriorityStream<'a,KT,VT,CAP>;
  fn into_iter(self) -> Self::IntoIter {
    PriorityStream(self)
  }
}// ref intoiter
