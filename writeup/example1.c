// special rules: process/key: is assumed High; return value is forced Low
//              debug/arg: requires Low

int process(int key) {               // specify process/key:High; return value is forced Low
  int special[] = {2, 3, 8, 12, 14}
  int chk = (key >> 10) && 0xf;   // generic rule makes chk:High
  int ok = false;
  int n = f();

  for (int i = 0; i <= n; i++) {
    debug ("checking %d", special[i]);   // may leak if f() >= 5: either generic flow rule or memory safety rule catches this
    if (chk == special[i]) {
      debug("found it"):             // implicit flow leak unless chk is never special 
      ok = true;                    // ok is high
    }  
    debug("done");                   // no leak
  }
  
  if (g()) {   
    debug("problem with %d", key);     // leak if g() is ever true
  }

  return ok;                         // ok is coerced low  
}
