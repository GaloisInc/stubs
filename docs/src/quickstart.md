# Quickstart

In this section, we will develop a Stubs program from scratch, with the purpose of defining a model of a clock for use in symbolic execution.

For our clock, we will model time as a simple integer, and each time we invoke `time`, the clock will increment before returning the current value. To do this, we will start by building defining a module to implement the counter, `clock.stb`. 
Firstly, we declare a global variable to hold the clock value, in order to access it later. 

```c
int clockInternal;
```

Then, we add our `time` method. Notice that addition is implemented as a function call. This allows architectures to define custom implementations of core operations, referred to as the preamble.

```c

fn int time(){
    clockInternal = plus(clockInternal,1);
    return clockInternal;
}
```

Next, we need a way to initialize the clock, and so we may try the following:

```c
fn unit initialClock(){
    clockInternal=0;
    return ();
}
```

Notice that Stubs, unlike C, uses `unit` rather than `void`, and has a unit literal `()`. Nevertheless, there is still an issue here, namely that we must ensure `initialClock` is actually called. If we leave this to the client code, it is possible that it is called several times, resetting our clock, or that it is never called, leading to an error in `time`.

To work around this, we introduce the keyword `init`, like so: 

```c
init fn unit initialClock(){
    clockInternal=0;
    return ();
}
```

This keyword is only valid if the function takes no arguments, and returns `unit`. Before symbolic execution, all functions marked `init` are run. Order of this is not guaranteed, in general.

Now, our module looks like this:

```c 
int clockInternal;

fn int time(){
    clockInternal = plus(clockInternal,1);
    return clockInternal;
}

init fn unit initialClock(){
    clockInternal=0;
    return ();
}
```

This is sufficient for a small clock model, but it has some issues when trying to build on top of it. Suppose we have designed this module in an atomic way, as we have, with the intent of having another module to build on top of it, or using it in conjunction with several other modules. Something we want to take care of is that other modules do not inadvertantly interfere with `clockInternal`, such as setting it to another value, breaking our abstraction. One way to resolve is through opaque types. We can change our module to the following: 

```c
type clock = int;
clock clockInternal;

fn int time(){
    clockInternal = plus(clockInternal,1);
    return clockInternal;
}

init fn unit initialClock(){
    clockInternal=0;
    return ();
}
```

Now, our clock variable has its own type, `clock`. Inside of this module, we are able to use this variable as if it were an `int` (as it ultimately is), but other modules cannot utilize this knowledge. As we do not add any way to manipulate the variable outside of `time` and `initialClock`, we can hide the details of how a clock is implemented to other modules.

With our previous definition of the module, the following other module would work, whereas with the opaque `clock` type, it will not.

```c 
fn int bumpTime (int x){
    clockInternal = plus(clockInternal,x);
    return clockInternal;
}
```

We can still perform this operation, using the exposed interface as intended:

```c 
fn int bumpTime(int x){
    int i = x;
    int t = 0;
    while gt(i,0) {
        t = time();
        i = minus(i,1);
    }
    return t;
}
```

This extends the interface of our clock module, without taking advantage of implementation details or leaking the abstraction. Another point to note is that parameters are immutable (necessitating the declaration of `i`).

If you've followed this quickstart guide, you now have your first module, and have seen custom types, global data, functions (and init functions), as well as several language constructs. Continuing on to the next section (Language), you can find a more comprehensive definition of the Stubs language's concrete syntax, and a discussion of more advanced features.
