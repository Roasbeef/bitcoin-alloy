module script_vm

// Byte represents a single byte. This is effectively the set of all bytes. 
sig Byte {}

// ZeroByte is a special value that indicates the "zero" element which is seen
// as being false. This is also useful to model the empty byte array as well.
one sig ZeroByte extends Byte {}

// isZero is a predicate that determines if a byte element is zero or not.
// This'll be used to eval the fail+success scenario of the stack.
pred isZero[byte: Byte] {
  byte in ZeroByte
}

// isTruthy is what we'll use later on to determine is execution has succeeded
// or not. This states that: there exits some byte within the byte array, that
// isn't the zero byte.
pred isTruthy[b: ByteArray] {
  some byte: b.bytes.elems | not isZero[byte]
}

// OpCode is a subset of Byte, it constains the set of all valid op codes. 
abstract sig OpCode extends Byte {}

// Next we define the set of op codes that we'll be using within our
// constrained model. We use one here, as each of these are singletons. 
one sig OP_TOALTSTACK, OP_FROMALTSTACK, OP_CAT extends OpCode {}

// ByteArray is a byte array, used to model data pushes within script, and also
// normal op codes as well.
sig ByteArray {
  // bytes is the internal sequence of a ByteArray. We use the `seq` syntax
  // here as we want to allow duplicates. Otherwise it'll me modeled as a set.
  // A sequence is relation from Int -> Elem, we also get some other helper
  // functions as well.
  bytes: seq Byte,
} {
  // We add a constraint that a given byte array on the stack must be less then
  // 520 bytes, which is the post taproot limit.
  #bytes <= 520 
}

// len is a helper function used to get the total size of a byte array.
fun len (arr: ByteArray): Int {
  #arr.bytes
}

// PkScript is the public key script predicate that needs to be satisfied.
one sig PkScript extends ByteArray {}

// Witness is the input to the public key script.
one sig Witness extends ByteArray {}

// Stack is the stack in Bitcoin Script used for execution. We assume post
// BIP-0342 rules, which includes: OP_SUCCESS, 1k combined stack+altstack
// limit, etc.
sig Stack {
  // items is the set of items in the stack.
  items: seq ByteArray,

  // top is a pointer to the top of the stack (end of the array).
  top: one Int
} {
  // The top can't be a negative number (no wrap around semantics, etc).
  top >= 0

  // The top pointer must be less than the number of items to be well formed.
  top <= #items

  // A given stack cannot have more than 10k elements.
  top <= 1000 

  // As an extra constraint, we'll make sure that we don't exceed the total
  // amount of bytes that can exist across the stack. We have a max of 1k
  // elements, at 520 bytes each, so a max of 520 KB.
  //
  // This can be read as: for each element i in the set of elements in the
  // stack, create a new set of all the lengths of each element, sum that, then
  // ensure the final constraint is met.
  {sum i: items.elems | len[i]} <= 520000
}

// VM is an abstract Script VM instance. It contains the stack, and also the
// altstack.
sig VM {
  // stack is the main stack in the VM.
  stack: Stack,

  // altstack is the altstack, used for sub computations typically.
  altstack: Stack,

  // pkScript is the predicate that we'll attempt to satisfy.
  // pkScript: PkScript,
  pkScript: seq ByteArray,

  // witness is the input into the predicate (pkScript).
  // witness: Witness,
  witness: seq ByteArray,
} {
  // Per BIP-342, the size of the stack and the altstack cannot exceed 1k
  // elements.
  #stack + #altstack < 1000
}

// StackConsistency is a basic fact about the VM we've created up until now. It
// states that: or any instance of the VM, if the stack has no elements, then
// the top of the stack is zero. We add the same assertion for the altstack as
// well.
fact StackConsistency {
    all vm: VM |
    (no vm.stack.items) <=> (vm.stack.top = 0) and
    (no vm.altstack.items) <=> (vm.altstack.top = 0)
}

// push pushes an element onto the top of the stack.
pred push[stack: Stack, elem: ByteArray] {
  stack'.items = stack.items.add[elem]
  stack'.top = stack.top + 1
}

// initVM is the main constructor of the VM. We take a pkScript, and a witness,
// set the witness as the initial stack, then set up the other counters.
pred initVM[vm: VM] {
  // The alt stack starts out empty.
  vm'.altstack.top = 0
  no vm'.altstack.items 

  // The stack starts with the witness, and points to the top of the witness.
  vm'.stack.items = vm.witness
  vm'.stack.top = #vm.witness
}

// evalOpcode is used to execute the main step in the VM loop. We'll take an op
// code, then execute it based on the existing stack contents.
pred evalOpcode[vm: VM, op: OpCode] {
  // OP_TOALTSTACK takes the top item of the stack and pushes it onto the alt
  // stack.
  op = OP_TOALTSTACK => {
    // Remove the last item from the main stack in the next time step,
    // decrementing the top counter along the way.
    vm'.stack.items = vm.stack.items.butlast
    vm'.stack.top = vm.stack.top - 1           

    // Take the last item of the stack, then add it to the alt stack, then
    // increment the alt stack top pointer by one.
    vm'.altstack.items = vm.altstack.items.append[vm.stack.items.last] 
    vm'.altstack.top = vm.altstack.top + 1      
  }

  // OP_FROMALTSTACK is the opposite of OP_TOALTSTACK.
  op = OP_FROMALTSTACK => {
    // Remove the top item of the altstack, then decrement the top pointer.
    vm'.altstack.items = vm.altstack.items.butlast 
    vm'.altstack.top = vm.altstack.top - 1        

    // Add the last time of the alt stack to the main stack, incrementing the
    // counter again.
    vm'.stack.items = vm.stack.items.append[vm.altstack.items.last] 
    vm'.stack.top = vm.stack.top + 1               
  }

  op = OP_CAT => {
    // There must be greater than two elements remaining in the stack.
    #vm.stack.items >= 2 and

    // Get the top two elements of the stack.
    let a = vm.stack.items.last,
        b = vm.stack.items.butlast.last,

        // Contact the byte sequences.
        ab = top1.bytes + top2.bytes | {
      // Add a requirement that the new set of bytes is below 520 bytes.
      #ab <= 520 and

        // New stack with result replacing the top two elements.
        vm'.stack.items = vm.stack.items.butlast.butlast.append[ab]
        vm'.stack.top = vm.stack.top - 1 
      }
    }
}

run {} for 5
