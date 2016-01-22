def O(i):
    if i==0:
        return "((b0 + a0) + b0)"
    else:
        return "(b{} => ((b{} + a{}) + b{}))".format(i-1,i,i,i)

def NN(k,n):
    if k==n:
        return N(k)
    else:
        return "({} + ({}))".format(N(k), NN(k+1,n))

def N(i):
    return "(b{} & a{})".format(i,i+1)


n = 3

print "%assume end : a{}.".format(n)

for i in range(n):
    print "%assume O{} : {}.".format(i,O(i))

print "%prove a0 + {}.".format(NN(0,n-1))
