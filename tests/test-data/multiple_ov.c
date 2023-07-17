int g(){
    return 2;
}

int f (int x) {
    return g()+x;
}
void j (){}

int main(){
    j();
    int i = g();
    return f(5);
}