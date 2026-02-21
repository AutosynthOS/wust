
convert instructions/operations into structured execution data:

Basic ops -> execute inline


Block -> converted into a thing that references the block map idx in a function definition -> these might map to like PC values?
End Block -> corresponds to the next instruction after a given block? or maybe we like entirely just omit that instruction, and refer to the block's (maybe &[Operations]) slice of some kind?
Br -> relative depth -> maps to a block idx again, load PC, continue execution from there
BrIf -> relative depth -> maps to a block idx again, load PC, continue execution from there
Call -> this ones interesting, we get the function IDX, load the function definition, we know it has return_size, locals_size + inline frame size, so we create an inline stack frame at a certain offset, set the param locals to the args/values of the fn call, set the return_sp to current sp then set our sp to the new inline frame offset... then we could like, either recurse, using a new funcidx/function definition, and begin executing it's first block etc.
Drop -> here tho.. we kinda need to like maybe know what the size of the thing that we're dropping is? our function parsing/validation/preparation logic might give the Operation::Drop instruction maybe like the type value/size of the thing we're dropping? 

Idea is like, maybe a function definition might end up looking like:

```rust
struct FunctionDefinition {
    return_size: usize,
    locals_size: usize,
    inline_frame_size: usize,
    blocks: Vec<Block>,
}

struct Block {
    pc: usize,
    body: &[Operation],
}
```