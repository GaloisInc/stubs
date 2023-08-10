# Simple Programs

This example shows a definition for a simple override that defines a function `f`, which is an identity function for an integer.

```c
fn int f(int x){
    return x;
}
```

For a more involved example, below are definitions for even and odd, defined in a mutually recursive manner. 

```c
fn bool odd(int x){
    if eq(x,0) {
        return false;
    } else {
        if even(minus(x,1)) {
            return true; 
        } else {
            return false;
        }
    }
}

fn bool even(int x){
    if eq(x,0){
        return true;
    } else {
        if odd(minus(x,1)){
            return true;
        } else {
            return false;
        }
    }
}
```

Note that there is no syntactic sugar for else-if. Additionally, unlike C, Stubs doesn't use parentheses around a condition.

The following is a more involved example, relying on two externally declared functions with a special type. The main point of interest here is that
rather than `void`, Stubs uses `unit`, which has a literal `()`. Additionally, for functions where the return is meaningless, as in C a call is a valid statement.

```c
extern unit print(@string s);
extern @string itos(int x);

fn unit f(int x){
    print(itos(x));
    return ();
}
```