# bitcoin-alloy

## Overview 

The `bitcoin-alloy` project aims to create a [lightweight formal
model](https://en.wikipedia.org/wiki/Formal_methods#:~:text=Lightweight%20formal%20methods,-Some%20practitioners%20believe&text=Examples%20of%20this%20lightweight%20approach,and%20the%20CSK%20VDM%20Tools.)
of Bitcoin Script to use as a tool to research/analyze various proposals (as
well as the current state post
[BIP-0342](https://github.com/bitcoin/bips/blob/master/bip-0342.mediawiki) to
extend Bitcoin Script with additional expressively and introspection
capabilities. Once the project is able to closely model the complete semantics
of Bitcoin Script, it will also serve as formal specification of Bitcoin Script
itself.  The goal of the `bitcoin-alloy` project is to serve as formalized
setting to explore current and future approaches to scripting capabilities
within Bitcoin.

Future versions may also be able to be used as a tool to model on-chain state
machines on Bitcoin created via future transaction introspection capabilities
(covenants).

This project was initially created during the
[btcplusplus@Austin](https://btcplusplus.dev/conf/atx24) hackathon.

This project was inspired by [this Delving Bitcoin
post](https://delvingbitcoin.org/t/analyzing-simple-vault-covenant-with-alloy/819/1)
which used Alloy model [rijndael's OP_CAT vault
implementation](https://delvingbitcoin.org/t/basic-vault-prototype-using-op-cat/576).

## Project Goals
- **Model Bitcoin Script VM**: Develop a comprehensive model that can execute
  Bitcoin scripts accurately within the Alloy framework.

- **Research Scripting Costs + Covenants**: Extend the model to analyze
  different Bitcoin scripting cost approaches. The analysis will help in
  analyze strategies to reduce the computational overhead and prevent DoS
  vulnerabilities in script processing.

- **Use of Alloy 6 Features**: Employ Alloy 6 capabilities, including facts,
  assertions, scenarios, and temporal logic, to provide deeper insights and
  rigorous verification of script execution behaviors and cost dynamics.

## Current State

As of now, the `bitcoin-alloy` project is in the early stages of development
(full scenarios aren't built up yet).

The initial phase focuses on:

- Setting up the basic structure of the Bitcoin Script VM in Alloy.

- Implementing core script operations and fundamental execution paths.

- Modeling basic stack operations such as `OP_TOALTSTACK` and `OP_CAT`. 

- Predicates to limit the total number of stack, max element size, etc are used
  in modeled.
