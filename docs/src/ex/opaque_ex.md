# Opaque type Example

This example consists of two modules, one which defines a `Counter` type, with several operations, and one that utilizes this type.

First, we have the interface: 

```c
type counter = int;  

fn counter initCounter(){
    c = 0;
    return c;
}

fn counter inc(counter c){
    counter d=plus(c,1);
    return d;
}

fn int asInt(counter c){
    return c;
}
```

Note that the only way for another module to get the value in a counter is through `asInt`, as otherwise it is a `counter` not an `int`. Only this module knows they are equivalent types.

```c
fn int f(){
    counter t = initCounter();
    t = inc(inc(t));
    return asInt(t);
}

```