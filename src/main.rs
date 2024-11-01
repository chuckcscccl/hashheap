#![allow(dead_code)]
#![allow(unused_variables)]
#![allow(non_snake_case)]
#![allow(non_camel_case_types)]
#![allow(unused_parens)]
#![allow(unused_mut)]
#![allow(unused_assignments)]
#![allow(unused_doc_comments)]
#![allow(unused_imports)]

use hashheap::*;
use hashheap::consthashheap::*;

// test user-hash function on strings that produces collisions by design...
fn shash(s:&str) -> usize {
  let mut sum = 0;
  for c in s.chars() {
    sum += c as usize
  }
  //println!("userhash returning {}",&sum);
  sum
}//shash test function

fn main1() {
  let mut gpa = HashHeap::<&'static str, u16>::new_maxheap();
  //gpa.set_hash(|s|shash(s));
  gpa.set_rehash(|h,c|h+c*c/2 + c/2); 
  gpa.insert("larz",245);
  gpa.insert("mary",375);
  gpa.insert("narx",108);
  gpa.insert("sam",399);    
  gpa.insert("oarw",390);
  gpa.insert("nev",145);
  gpa.insert("haten",101);

  for n in ["mary","larz","narx","oarw","nev","haten","sam"] {
    println!("{}: {:?}",n, gpa.get(&n));
  }

  gpa.modify(&"oarw",|g|{*g=191});
  println!("\n-------------\npop: {:?}",gpa.pop());
  println!("pop: {:?}",gpa.pop());

  println!("remove(larz): {:?}", gpa.remove(&"larz"));

  for n in ["mary","larz","narx","oarw","nev","haten","sam"] {
    println!("{}: {:?}",n, gpa.get(&n));
  }

  for k in gpa.keys() { println!("key {}",k);}
  for (k,v) in gpa.iter() {println!("key {}, value {}",k,v);}

  println!("swap: {:?}", gpa.top_swap("fred",54));
  println!("swap: {:?}", gpa.top_swap("haten",0));  

  while gpa.len()>0 {println!("final pop: {:?}",gpa.pop());}

  //gpa.diagnostic();

  //let mut rs = std::collections::hash_map::RandomState::new();
  //println!("derive_hash: {}",derive_hash(&mut rs, &"larz"));
  //println!("derive_hash: {}",derive_hash(&mut rs, &"larz"));  
}//main





fn main() {
  let mut chh:ConstHashHeap<&'static str,f32,8> = ConstHashHeap::new(true);
  chh.insert("mary",3.0);
  chh.insert("larz",2.0);
  chh.insert("narx",2.5);
  chh.insert("parv",3.4);
  
  //chh.diagnostics();
  let mut dhh = chh.resize::<16>();
  dhh.insert("oarw",3.7);
  dhh.insert("qaru",2.6);
  dhh.insert("nev",0.2);
  
  dhh.diagnostics();
  dhh = dhh.refresh();  // re-insert keys
  dhh.diagnostics();
  
  dhh.remove(&"narx");
  println!("get narx: {:?}", dhh.get(&"narx"));
  println!("get mary: {:?}", dhh[&"mary"]);
  //dhh.diagnostics();

  /*
  while let Some((key,val)) = dhh.pop() {
    println!("{} : {}", &key, &val);
  }
  */

  for (k,v) in dhh.iter() {
        println!("iter {} : {}", k, v);
  }

  for (k,v) in dhh.priority_stream() {
        println!("next priority: {} : {}", &k, &v);
  }
  println!("final size: {}",dhh.size());
}//main for consthashheap

