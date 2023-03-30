# Compression module

This module is called when the command compress is passed in the command line. It implements the algorithm Lower Units described in [https://link.springer.com/chapter/10.1007/978-3-642-22438-6_19]{https://link.springer.com/chapter/10.1007/978-3-642-22438-6_19}. In this guide, we will describe how the code and the algorithm work.

### Lower Units

The algorithm can be described in 3 general steps:

1. unit_nodes <- collect_units(proof)
1. fix(proof)
1. reinsert_units(proof, unit_nodes)

Now, we describe each step carefully.

##### Collect units
A DFS is performed starting at the conclusion node. Every time a unit node is reached, it is marked as visited. If it visited when already marked as visited, it is added to the unit_nodes queue. The paper does not specify if it should be added when it is visited for the first, second or last time, so we chose to do it at the second time. When it is added to the queue, it is replaced my a "deleted node marker" (DNM). 

##### Fix proof
The `fix_proof` is not described at the paper at all. So, we had to guess what we were supposed to do. The goal of this functino is to remove all DNMs. 

We do this by traversing the proof with a DFS starting in the conclusion node. Every time a node is reached, the function is called to its parents. After that, if one of the parents is a DNM, the node is replaced by the other parent. The problem is that when replacing a node by its parent, the parent may have been replaced as well, and the node must be replaced by its grandparent. To do this efficiently, we use a [union find]{https://en.wikipedia.org/wiki/Disjoint-set_data_structure}. This structure is represented in `acutal: Vec<usize>` and the `i`-th entry represents who replaced the node `i` (it is `i` if it was not replaced).

After that, the function `add_node` is called on the conclusion node. When this function is called for a node, it is recursevely called for its parents. After the call is finished, it inserts this node in a new `Vec` with all proof commands. When doing this, it must be aware that the id of its parents has changed and it may have been deleted. Besides that, it can also be called twice on the same node, bbut the node can only be inserted once. It returns the index where it was placed in the `new_commands` vector. After the call has finished, `new_commands` has all commands that were not deleted.

##### Reinsert units
The last step is to reinsert the removed unit nodes. For every unit_node, it is added to the proof using the `add_node`function, so that it ancestors are added as well. After that, the resolution step is made using the unit node and the current last node of the proof, using the function `binary_resolution_with_unit`. In the end, the command is added to the `new_command` vector. When the last unit node is added and the resolution is made, the algorithms ends.


### Observations
There are still some problems with the code that must be solved.
1. Some functions, like `add_node` and `find` are recursive. This may be a problem because the program can run out of memory (`find` is probably ok because it is short and it probably will not be called many time recursively).
1. The program still does not support subproofs. In function like `binary_resolution_from_old`, the new commands are added in the subproof with index 0, the proof itself. This has to be changed.
1. Results are not properly parsed. Functions like `binary_resolution_with_unit` call the function `binary_resolution`, that can return an error. But this is not properly parsed. Besides that, functions like `get_pivots` may panic and this may not be the best way to deal with problems.
1. Running some checks on the test_examples showed that there may be problems with the `get_pivots` function. Also it cannot handle resolutions made from more than two parents. 
1. The program was not properly tested. 