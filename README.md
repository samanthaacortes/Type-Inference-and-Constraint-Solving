Implementug a type checker for Nano, just like the :t command in GHCi. If a program fails to type-check, you will be able to identify the error (e.g., if your program tried to add 3 and False); and if a program does type-check, you will be able to say what its type actually is.

As a bonus, the checker is designed in such a way that it can support type polymorphism, so that generic functions like \x -> x and map can be defined without having to write down specialized copies for every type of data you want to invoke them on.
