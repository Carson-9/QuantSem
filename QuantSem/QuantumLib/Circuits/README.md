<div id="toc" align="center">
<ul style="list-style: none">
<summary>
<h1 style="center"> 
$\bigotimes\mathcal{H}^\dagger\bigoplus \quad \Huge{\color{#9638D6} \langle \text{Quantum Circuits} \rangle} \quad \lambda.\Pi\Sigma$
</h1>
</summary>
</ul>
</div>

## 🎯 Purpose 

This layer describes Quantum Circuits as an Inductive type, defines the action of a circuit over some state, and defines a notion of Equivalence between circuits. Thanks to this inductive (and local) structure, some powerful equivalence theorems are established, allowing to define Normal forms and reduction tactics for circuits.

## 📋 Content 

```
.
├── AbstractBasis.lean      -- Circuits over spaces with some abstract basis
├── Basic.lean              -- General Circuits, General equivalence of circuits, main rewriting theorems
├── ListAbstractBasis.lean  -- Circuits over a List of register rather than some global register
└── README.md
```
