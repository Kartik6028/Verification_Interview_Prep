#write a code to give closest prime from a number N.


def is_prime (n):
    if n<2:
       return False
    for i in range (2, (n**0.5)+1):
      if n % i ==0:
        return False
        break
    return True

def closer_prime (n):
    if is_prime (n):
      return n
   
    count_up=n
    count_down=n

    while is_prime(count_up)==0:
      count_up=count_up+1
    
    while is_prime(count_down) ==0:
      count_down=count_down-1
    c_prime= count_up if count_up <count_down else count_down
    return c_prime
   

#write a code to check palindrome - 2 pointer

def check_palin (n):
    left=0
    right=len(n)-1

    while left!=right:
        left=left+1
        right=right+1
        if n[left] != n[right]:
           return False
    return True

#reverse a string/array of chars in place

def reverseinplace(n):
   left=0
   right=len(n)-1

   while right!=left:
      temp=n[right]
      n[right]=n[left]
      n[left]=temp

      right= right-1
      left = left+1

# remove duplicates from a sorted array
def remdep(n):
   if not n:
      return 0
   i=0
   for j in range (1,len(n)):
      if n[j] != n[i]:
         i+=1
         n[i] = n[j]

   return i+1

#remove an element from an array in-place.

def rem_item(a,n):
   j=0
   for i in range (len(n)):
      if n[i] !=a:
         n[j]=n[i]
         j+=1
   return j
         

#merge two sorted arraays
def merge_sort_arr(a,b):
    j=0
    k=0
    merged_array = 0
    while k< len(a) and j < len(b):
       if a[k] < b [j]:
        merged_array.append (a[k])
        k+=1
       else :
        merged_array.append(b[j])
        j+=1
    
    while k < len(a):
       merged_array.append(a[k])
       k+=1
    while j< len(b):
       merged_array.append(b[j])
       j+=1
    
#targetsum
def targetsum (n, lis):
   left =0
   right = len(lis) -1
    
   while left < right:
      if lis[left] + lis[right] == n:
         return True
      
      elif lis[left] + lis[right] < n:
         left+=1
      else:
         right-=1


   return False

#targetsum non sorted
def targetsum_nosort(n,lis):
   hset = set()
   for x in lis:
      need = n -x
      if need in hset :
         return True
      hset.add(x)
   return False

#fibonacci      
def fib (n):
   
   if n <=1:
      return n
   return fib(n-1) + fib(n-2) 

def lin_fib (n):
   a=0
   b=1
   for i in range (2,n):
      c=a+b
      a=b
      b=c
   return c


#files

#splicing

#ooo?
