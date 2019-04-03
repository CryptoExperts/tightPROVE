# tightPROVE

tightPROVE is a formal verification tool for the tight probing
security of masked implementations. 

tightPROVE was introduced in the following publication:

[Tight Private Circuits: Achieving Probing Security with the 
Least Refreshing](ia.cr/2018/439)   
By Sonia Belaïd, Dahmun Goudarzi, and Matthieu Rivain.   
In the proceedings of ASIACRYPT 2018.
 
## Content

This repository contains the code of __tightPROVE__ implemented in SageMath:

- tightPROVE.sage

and a few examples of input files:

- example1.txt: the circuit corresponding to example 1 in the publication;
- example2.txt: the circuit corresponding to example 2 in the publication;
- example3.txt: the circuit corresponding to example 2 augmented with a refresh gadget;
- aes.txt: the AES s-box circuit considered in the publication.

## Usage 

Using the tool requires having [SageMath](http://www.sagemath.org/) installed (v6.10 or higher). Then simply run the following command line:

	sage tightPROVE.sage file.txt

where `file.txt` is the input circuit file.

## Input syntax 

The input circuit format is as follows. Each line represents an operation or refresh gadget with the syntax 

- `xor i j` for a Boolean addition gadget,
- `and i j` for a Boolean multiplication gadget, 
- `ref i` for a refresh gadget,

where `i` and `j` are the indexes of the two operands, i.e., the output of operations from the _i_-th and _j_-th lines. 

The inputs of the circuit are represented at the top of the file as

	in 0
	in 1
	...


## License 

[GPLv3](https://www.gnu.org/licenses/gpl-3.0.en.html)