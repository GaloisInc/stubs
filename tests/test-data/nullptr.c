int f(int* x){
    return *x;
}

// seg fault unless f is overridden
int main(){
    return f(0);
}