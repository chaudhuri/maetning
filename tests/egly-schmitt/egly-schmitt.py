#!/usr/bin/python
# -*- coding: utf-8 -*-

import argparse

parser = argparse.ArgumentParser(description="Create versions of the Egly--Schmitt formulas for the provers Mætning and BDDIntKt.")

parser.add_argument('-bddintkt',
                    action='store_true',
                    default=False,
                    help='create instance tailored for BDDIntKt.')

parser.add_argument('-fcube',
                    action='store_true',
                    default=False,
                    help='create instance tailored for fCube.')

parser.add_argument('size',
                    metavar='N',
                    type=int,
                    help='size of instance.')

parser.add_argument('-simplify',
                    action='store_true',
                    default=False,
                    help='simplify ternary disjunctions into binary disjunctions --- part of the normalisation scheme in BDDIntKt, but not in Mætning.')

parser.add_argument('-no-proof',
                    action='store_true',
                    default=False,
                    help='make the instance non-provable.')

parser.add_argument('-positive',
                    action='store_true',
                    default=False,
                    help='assign positive polarity to all atoms (Mætning only).')

parser.add_argument('-o',
                    metavar='FILE',
                    type=argparse.FileType('w'),
                    help='name of output file.')

args = parser.parse_args()



if args.o is None:
    filename = "es" + str(args.size)
    if args.positive:
        filename += "-positive"
    if args.no_proof:
        filename += "-false"
    if args.simplify:
        filename += "-simple"
    if args.bddintkt:
        filename += ".fml"
    elif args.fcube:
        filename += ".fc"
    else:
        filename += ".mg"
else:
    filename = args.o

print "Writing instance to file", filename

if args.bddintkt:
    orsym = "|"
else:
    orsym = "+"

def O_fcube(i):
    if i==0:
        if args.simplify:
            return "or(b0, a0)"
        else:
            return "or(or(b0, a0), b0)"
    else:
        if args.simplify:
            return "im(b{}, or(b{}, a{}))".format(i-1,i,i)
        else:
            return "im(b{}, or(or(b{}, a{}), b{}))".format(i-1,i,i,i)

def O(i):
    if i==0:
        if args.simplify:
            return "(b0 {orsym} a0)".format(orsym=orsym)
        else:
            return "((b0 {orsym} a0) {orsym} b0)".format(orsym=orsym)
    else:
        if args.simplify:
            return "(b{} => (b{} {orsym} a{}))".format(i-1,i,i,orsym=orsym)
        else:
            return "(b{} => ((b{} {orsym} a{}) {orsym} b{}))".format(i-1,i,i,i,orsym=orsym)


def NN_fcube(k,n):
    if k==n:
        return N_fcube(k)
    else:
        return "or({}, ({}))".format(N_fcube(k), NN_fcube(k+1,n))

def N_fcube(i):
    return "and(b{}, a{})".format(i,i+1)


def NN(k,n):
    if k==n:
        return N(k)
    else:
        return "({} {orsym} ({}))".format(N(k), NN(k+1,n),orsym=orsym)

def N(i):
    return "(b{} & a{})".format(i,i+1)

if args.fcube:
    O = O_fcube
    N = N_fcube
    NN = NN_fcube

n = args.size

f = open(filename,'w')

if not args.bddintkt:
    if args.positive:
        for i in range(n):
            print >> f, "%positive a{}.".format(i)
            print >> f, "%positive b{}.".format(i)
        print >> f, "%positive a{}.".format(n)

cpars = ")"
if args.fcube:
    print >> f, "decide(",


if not args.no_proof:
    if args.bddintkt:
        print >> f, "a{} =>".format(n),
    elif args.fcube:
        print >> f, "im(a{},".format(n),
        cpars += ")"
    else:
        print >> f, "%assume end : a{}.".format(n)

for i in range(n):
    if args.bddintkt:
        print >> f, "{} =>".format(O(i)),
    elif args.fcube:
        print >> f, "im({}, ".format(O(i)),
        cpars += ")"
    else:
        print >> f, "%assume O{} : {}.".format(i,O(i))

if not args.bddintkt and not args.fcube:
    if args.no_proof:
        print >> f, "%refute",
    else:
        print >> f, "%prove",

if args.fcube:
    print >> f, "or(a0, {})".format(NN(0,n-1)), cpars,
else:
    print >> f, "(a0 {orsym} {})".format(NN(0,n-1),orsym=orsym)

if not args.bddintkt:
    print >> f, "."
