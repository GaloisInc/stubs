int f(int x) {
    return x*2;
}

int g(int y) {
    return y + 1;
}

int main(){
    int i = g(2);
    return f(i);
}