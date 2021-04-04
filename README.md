# LBT-assignments

## Assignment 1
In this homework you will build an interpreter a simple functional language equipped with
security permissions. Each function definition is equipped with a set of permissions (e.g.
{read, write}, {}) over a set of security relevant actions. We also assume that the language is
equipped with a primitive construct to check a permission. The interpreter executes if
permissions are enabled; otherwise, execution fails.