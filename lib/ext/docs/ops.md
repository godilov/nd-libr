# NdExtensions Operations

**`Nd-kind` extensions for [`std::ops`]**

## Overview

The module defines `Nd-kind` operations traits and aggregate traits on top of `Std-kind` and `Nd-kind`.

**Features**:

- Defines operations by reference.
- Defines operations for any type.
- Defines operations for modes: `Default`, `Checked`, `Strict`, `Wrapping`, `Saturating`, `Overflowing`, `Unbounded`.

It allows avoiding HRTB and expensive clonning/copying in generic context.

**Operations per Mode**:

| Mode          | Operations                                          |
| ------------- | --------------------------------------------------- |
| `Default`     | `+`, `-`, `*`, `/`, `%`, `<<`, `>>`, `\|`, `&`, `^` |
| `Checked`     | `+`, `-`, `*`, `/`, `%`, `<<`, `>>`                 |
| `Strict`      | `+`, `-`, `*`, `/`, `%`                             |
| `Wrapping`    | `+`, `-`, `*`, `/`, `%`                             |
| `Saturating`  | `+`, `-`, `*`, `/`, `%`                             |
| `Overflowing` | `+`, `-`, `*`, `/`, `%`, `<<`, `>>`                 |
| `Unbounded`   | `<<`, `>>`                                          |

**Panic per Mode**:

| Mode                    | Panic                                        |
| ----------------------- | -------------------------------------------- |
| `Default` (**debug**)   | **Must**                                     |
| `Default` (**release**) | **Must not**                                 |
| `Checked`               | **Must not**, returns `None`                 |
| `Strict`                | **Must**                                     |
| `Wrapping`              | **Must not**, returns **wrapped value**      |
| `Saturating`            | **Must not**, returns **saturated value**    |
| `Overflowing`           | **Must not**, returns **flag** and **value** |
| `Unbounded`             | **Must not**, returns **unbounded value**    |

## Related

Instead of implementing `Std-kind` and `Nd-kind` operations directly, use `ndops` procedural macros.
