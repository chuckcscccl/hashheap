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
use std::collections::hash_map::RandomState;
use core::hash::{BuildHasher, Hash, Hasher};

// inthash
/* new design.

keys stored in inthash custom hash table.
values in heap in the form of ?? how not to duplicate keys?

Design uses const generics, so key locations never change in hash table.
if keys shift locations, values must also shift location.

inthash contains actual key -> vi index of corresponding value.

heap contains entries of the form (value, ki), ki is index of where
key is store in inthash array.

keylocs array not needed, since key locations are kept in heap
*/

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


#[derive(Clone, Debug)]
pub struct ConstHashHeap<KT,VT, const CAPACITY:usize = 1024>
{
   keys : [Option<(KT,usize)>;CAPACITY],
   vals : [Option<(VT,usize)>;CAPACITY],
   maxhs : [usize;CAPACITY],
   size : usize,
   autostate: RefCell<RandomState>,
   lessthan : fn(&Option<(VT,usize)>,&Option<(VT,usize)>) -> bool,
}
impl<KT:Hash+Eq, VT:PartialOrd, const CAP:usize> ConstHashHeap<KT,VT,CAP> {

  pub fn new(maxheap:bool) -> Self {
    ConstHashHeap {
      keys : [const { None }; CAP],
      vals : std::array::from_fn(|_|None),
      maxhs : [0;CAP],
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
    let mut pi = parent(i);
    while (i>0 && (self.lessthan)(&self.vals[pi],&self.vals[i])) {
       self.swap(i,pi);
       i = pi;
       pi = parent(i);
    }
    i
  }//swapup

  fn swapdown(&mut self, mut i:usize) -> usize {
    let mut si = Some(0);
    while si.is_some() {
      si = None;
      let lf = left(i);
      let rt = right(i);
      if (lf<self.size && (self.lessthan)(&self.vals[lf],&self.vals[i])) {
        si = Some(lf);
      }
      if(rt<self.size && (self.lessthan)(&self.vals[rt],&self.vals[i])
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

  fn adjust(&mut self, i:usize) -> usize {
    let k = self.swapup(i);
    if k==i {self.swapdown(i)} else {k}
  }

  pub fn size(&self) -> usize {self.size}

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
        None if hashes <= self.maxhs[h0] => {
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
      Some(vi) if *vi==self.size && self.size*4 > 3*CAP => {
        return false;
      }
      Some(vi) if *vi == self.size => {
        self.size+=1;
        if target_index>=0 {h = target_index as usize;}
      },
      _ => {},
    }//match
    if hashes > self.maxhs[h0] {
      self.maxhs[h0] = hashes;
    }
    keyfoundloc.inspect(|vi|{
        self.keys[h] = Some((key,*vi));
        self.vals[*vi] = Some((val,h));
        self.adjust(*vi);
      });
    true
  }//set

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
        None if hashes <= self.maxhs[h0] => {
          h=Self::rehash(h);
          hashes += 1;        
        }
        None => { break; }
      }//match
    }//loop
    answer
  }//get
  
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
        None if hashes <= self.maxhs[h0] => {
          h=Self::rehash(h);
          hashes += 1;        
        }
        None => { break; }
      }//match
    }//loop
    if let Some(vi) = keyfoundloc {
      self.vals[vi].as_mut().map(|p|f(&mut p.0));
      self.adjust(vi);
      true
    }
    else {false}
  }// modify
  
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
        None if hashes <= self.maxhs[h0] => {
          h=Self::rehash(h);
          hashes += 1;        
        }
        None => { break; }
      }//match
    }//loop
    if let Some(vi) = keyfoundloc {
       let mut ak = None;
       let mut av = None;
       std::mem::swap(&mut ak, &mut self.keys[h]);
       std::mem::swap(&mut av, &mut self.vals[vi]);
       answer = ak.zip(av).map(|(a,b)|(a.0,b.0));
       // adjust heap;
       if (vi+1 != self.size) {
          self.swap(vi,self.size-1);
          self.adjust(vi);
       }
       self.size -= 1; 
    }
    answer
  }//remove

  pub fn pop(&mut self) -> Option<(KT,VT)> {
    let mut answer = None;
    if self.size < 1 { return answer; }
    if let Some((_,ki)) = &self.vals[0] {
       let mut ak = None;
       let mut av = None;
       std::mem::swap(&mut ak, &mut self.keys[*ki]);
       std::mem::swap(&mut av, &mut self.vals[0]);
       answer = ak.zip(av).map(|(a,b)|(a.0,b.0));
       if (self.size>1) {
            self.swap(0,self.size-1);
            self.swapdown(0);
       }
       self.size -= 1;     
    }
    answer  
  }//pop

  pub fn peek(&self) -> Option<&VT> {
    if self.size < 1 { None }
    else {
      self.vals[0].as_ref().map(|p|&p.0)
    }
  }//peek

  pub fn load_factor(&self) -> f32 {
    (self.size as f32) / (CAP as f32)
  }

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
           hp2.maxhs[h0] = hashes;
         });
         std::mem::swap(&mut hp2.keys[h],&mut self.keys[*ki]);
         self.vals[i].as_mut().map(|p|{p.1 = h;});
      } // if-let
      std::mem::swap(&mut hp2.vals[i], &mut self.vals[i]);      
    }//for
    hp2
  }//resize

}// main impl
