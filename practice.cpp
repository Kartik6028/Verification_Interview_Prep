
#include <iostream>
#include <vector>
#include <string>


using namespace std;

struct Node {
    int data;
    Node *next;

    Node (int data) {
        this -> data = data;
        this -> next = nullptr;
    }

};



// 0 1 1 2 3 5 8 13 21 34 55
long long fib_memo (long long n, vector <long long> &memo) {
    if (n<=1) return n;

    if (memo[n] != -1) return memo[n];  
    memo[n]= fib_memo(n-1,memo) + fib_memo(n-2,memo);
    return memo[n];
}
long long fib(long long n) {
    vector<long long> memo(n+1, -1);
    return fib_memo(n, memo);
}
void swap (int *a, int *b)
{
    int temp;
    temp = *a;
    *a= *b;
    *b=temp;
}

long long trad_fib (long long n) {
    if (n <=1) return n;
    return fib(n-1) +fib(n-2);
}

int main()

{
    int a = 5;
    int b= 10;
    cout << "nth Fibonacci :-" <<fib(60)<< endl;

    cout<< "value of a :-"<<a<<endl<<"value of b :- "<<b<<endl;
}