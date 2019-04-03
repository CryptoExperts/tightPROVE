###############################################################################
#
# Implementation of tightPROVE (tight PRobing VErification) tool in SageMath
#
# tightPROVE is a formal verification tool for the tight probing  
# security of masked implementations. 
#
# tightPROVE was introduced in the following publication:
# 
#    "Tight Private Circuits: Achieving Probing Security with the 
#    Least Refreshing". 
#    By Sonia Belaïd, Dahmun Goudarzi, and Matthieu Rivain. 
#    In the proceedings of ASIACRYPT 2018.
#    Available at ia.cr/2018/439
#
# Copyright (C) 2018 CryptoExperts
# 
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program.  If not, see <https://www.gnu.org/licenses/>.
#
###############################################################################

import sys

###############################################################################
###############################################################################
###      OBJECT CLASSES                                                     ###
###############################################################################
###############################################################################


# --------------------------------------------------------------------------- #
#      CLASSES CIRCUIT                                                        #
#        * Variables: opA, opB (Boolean vectors)                              #
# --------------------------------------------------------------------------- #

def generate_list_ins_from_file(circuit_file):
    list_instructions = []
    with open(circuit_file) as f:
        lines = f.readlines()
    for l in lines:
        args = l.split()
        if len(args) == 2: list_instructions.append(Instruction(str(args[0]), int(args[1]), int(0)))
        elif len(args) == 3: list_instructions.append(Instruction(str(args[0]), int(args[1]), int(args[2])))
        else: raise Exception('Bad instruction')
    return list_instructions


class Instruction:
    def __init__(self, ins, opA, opB):
        wrong_type = 'Wrong intruction type: only xor|and|refresh allowed'
        assert(ins in ['xor','not','and','ref','in','out']), wrong_type
        self.ins = ins
        self.opA = opA
        self.opB = opB

class Circuit:
    def __init__(self, instructions):
        assert (type(instructions) == list), 'Instructions must be a list'
        self.instructions = instructions
        self.nb_inputs = sum([ins.ins == 'in' for ins in instructions])
                

        # METHOD 'evaluate'
        # Evaluates the circuit for two types of input: - 'input' is an Integer and the circuit is evaluated on bits
        #                                               - 'input' is a list and the circuit is evaluated on bitslice registers                                
        # Returns the evaluation of the circuit on 'input'
        
    def evaluate(self, input):
        if type(input) == Integer:
            invar = map(GF(2),input.bits()) 
            invar += [GF(2)(0)]*(self.nb_inputs-input.nbits())
        elif type(input) == list:
            assert (len(input) == self.nb_inputs), 'Bad number of inputs'
            invar = map(GF(2),input)
        else:
            raise Exception('Bad input type')
        iv = [None]*len(self.instructions)
        outvar = []
        pc = self.nb_inputs-1
        for ins in self.instructions:
            if   ins.ins == 'in' : iv[pc] = invar[0]; del(invar[0])
            elif ins.ins == 'xor': iv[pc] = iv[ins.opA] + iv[ins.opB]
            elif ins.ins == 'and': iv[pc] = iv[ins.opA] * iv[ins.opB]
            elif ins.ins == 'not': iv[pc] = iv[ins.opA] + GF(2)(1)
            elif ins.ins == 'ref': iv[pc] = iv[ins.opA]
            elif ins.ins == 'out': iv[pc] = iv[ins.opA]; outvar.append(iv[pc])
            else: raise Exception('Bad instruction')
            pc += 1
        if type(input) == Integer:
            return sum([Integer(outvar[i])*2^i for i in range(0,len(outvar))])
        else: # type(input) == list
            return map(int,outvar)          


        # METHOD 'generate_mult_set'
        # Transforms the circuit into a flattened circuit
        # Returns the list of pairs of operands that are inputs to multiplication in the flattened circuit

    def generate_pairs_operands(self):
        iv = [None]*len(self.instructions)
        outlist = []
        pc = 0
        for ins in self.instructions:
            if   ins.ins == 'in' : iv[pc] = 2**pc
            elif ins.ins == 'xor': iv[pc] = iv[ins.opA] ^^ iv[ins.opB]
            elif ins.ins == 'and': iv[pc] = 2**(self.nb_inputs); self.nb_inputs += 1; outlist.append([iv[ins.opA],iv[ins.opB]])
            elif ins.ins == 'not': iv[pc] = iv[ins.opA]
            elif ins.ins == 'ref': iv[pc] = 2**(self.nb_inputs); self.nb_inputs += 1
            elif ins.ins == 'out': continue
            else: raise Exception('Bad instruction')
            pc += 1
        return outlist

                

# --------------------------------------------------------------------------- #
#      CLASS MULT                                                             #
#        * Variables: opA, opB (Boolean vectors)                              #
# --------------------------------------------------------------------------- #

def boolvec_to_int(v):
    return sum([int(v[i])*2^i for i in range(0,len(v))])

def boolvec_list_to_int_list(l):
    return [boolvec_to_int(v) for v in l]

class Mult:

    def __init__(self, opA, opB):
        if len(opA) != len(opB): 
            raise Exception('Operands must have the same length!')
        if opA == opB: 
            raise Exception('Operands must be different!')
        self.opA = opA
        self.opB = opB

    def __getitem__(self, i):
        if i!=0 and i!=1: 
            raise Exception('Operand index out of range')
        if i==0: return self.opA
        if i==1: return self.opB

    def __repr__(self):
        return '(' + str(boolvec_to_int(self.opA)) + ',' + str(boolvec_to_int(self.opB)) +')'

    def __str__(self):
        return '(' + str(boolvec_to_int(self.opA)) + ',' + str(boolvec_to_int(self.opB)) +')'

# --------------------------------------------------------------------------- #
#      CLASS SET                                                              #
#        * Variables: mult_list (list of Mult objects)                        #
# --------------------------------------------------------------------------- #

class MultSet:

    def __init__(self, mult_list):
        self.mult_list = mult_list

    def __getitem__(self, i):
        return self.mult_list[i]

    def size(self):
        return len(self.mult_list)

    def vector_space(self): 
        return VectorSpace(GF(2),len(self.mult_list[0][0]))

    # METHOD 'all_operands'
    #   - return the list of all operands (w/o duplicates)

    def all_operands(self):
        list_operands = [tuple(op) for m in self.mult_list for op in [m[0], m[1]]]
        return map(vector,list(set(list_operands)))

    # METHOD 'iterate'
    # Iterate the attack search method for operand 'op' and (current) span 'span'
    # Return two sets of mult and a list of operands (Boolean vectors):
    #    - set of mults with one operand matching 'op' + 'span'
    #    - set of mults with no operand matching 'op' + 'span' (complement of the first set)
    #    - list of co-operands of operands matching 'op' + 'span'

    def iterate(self,op,span=None):

        match_mults = []
        mismatch_mults = []
        co_operand_list = []
        
        for mult in self.mult_list:

            if span == None:

                if mult.opA == op:
                    match_mults.append(mult)
                    co_operand_list.append(mult.opB)
                elif mult.opB == op:
                    match_mults.append(mult)
                    co_operand_list.append(mult.opA)
                else:
                    mismatch_mults.append(mult)

            else: # span != None:

                if (mult.opA - op) in span:
                    match_mults.append(mult)
                    co_operand_list.append(mult.opB)
                elif (mult.opB - op) in span:
                    match_mults.append(mult)
                    co_operand_list.append(mult.opA)
                else:
                    mismatch_mults.append(mult)

        return MultSet(match_mults), MultSet(mismatch_mults), co_operand_list

    def __repr__(self):
        return '[' + ','.join([str(m) for m in self.mult_list]) + ']'

    def __str__(self):
        return '[' + ','.join([str(m) for m in self.mult_list]) + ']'


###############################################################################
###############################################################################
###      SUBFUNCTIONS                                                       ###
###############################################################################
###############################################################################

# --------------------------------------------------------------------------- #
#         IMPORT SUBFUNCTIONS                                                 #
# --------------------------------------------------------------------------- #

def int_to_boolvec(basis,x):
    return sum([x.bits()[i]*basis[i] for i in range(0,x.nbits())])

def import_mult(pair_list):
    
    m = max(map(max,pair_list))
    dim = m.nbits()
    V = VectorSpace(GF(2),dim)
    e = V.basis()
    list_mult = []

    for (a,b) in pair_list:
        opA = int_to_boolvec(e,a)
        opB = int_to_boolvec(e,b)
        list_mult.append(Mult(opA,opB))

    return MultSet(list_mult)


###############################################################################
###############################################################################
###      MAIN FUNCTIONS                                                    ###
###############################################################################
###############################################################################


# --------------------------------------------------------------------------- #
#         SEARCH ATTACK                                                       #
# --------------------------------------------------------------------------- #

def search_attack(mult_set,verbose=False):

    # --------------------------------------------------------------- #
    # 'mult_set' is the set of multiplications (MultSet object)       #
    # 'comb' is the target combination (if None, try all)             #
    # --------------------------------------------------------------- #

    VS = mult_set.vector_space()

    if(verbose):
        print '--------------------------------------------------------'
        print 'list_comb = ', map(boolvec_to_int,mult_set.all_operands())

        
    for comb in mult_set.all_operands():

        if(verbose):
            print '--------------------------------------------------------'
            print 'comb = ', boolvec_to_int(comb)

        G, O, U = [], [], []  
        span = None
        remaining_mults = mult_set

        while(1):

            match_set, mismatch_set, co_operand_list = remaining_mults.iterate(comb,span)

            G.append(copy(match_set)) 
            O.append(copy(co_operand_list))

            U = [op for Oi in O for op in Oi] 
            span = VS.subspace(U)

            # Test attack   

            if comb in span:
                if (verbose): 
                    print '=> ATTACK'
                    print '   G:', G
                    print '   O:', map(boolvec_list_to_int_list,O) 
                    print '--------------------------------------------------------'
                    return 'Attack found: %s in span %s'%(boolvec_to_int(comb), boolvec_list_to_int_list(U))

            # Test stop condition 1
            
            if match_set.size() == 0: # M[i] empty => no attack on comb

                if (verbose): 
                    print '=> NO ATTACK (G%s = G%s)'%(len(G),len(G)-1)
                    print '   G:', G
                    print '   O:', map(boolvec_list_to_int_list,O) 
                break 
            
            # Test stop condition 2

            if remaining_mults.size() == 0: # no mult remaining
                if (verbose): 
                    print '=> NO ATTACK (no mults left)'
                    print '   G:', G
                    print '   O:', map(boolvec_list_to_int_list,O) 
                break 

            # Remaining mults 

            remaining_mults = copy(mismatch_set)
        if verbose: print '--------------------------------------------------------'
    return 'No attack found'


def main():
    list_instructions = generate_list_ins_from_file(str(sys.argv[1]))      
    test_circuit = Circuit(list_instructions)
    mult_set = import_mult(test_circuit.generate_pairs_operands())
    print search_attack(mult_set,verbose=True)


if __name__ == "__main__":
    main()
