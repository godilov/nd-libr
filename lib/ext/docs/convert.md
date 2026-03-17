# NdExtensions convert

**`Nd-kind` extensions for [`std::convert`]**

## Overview

The module defines `Nd-kind` conversion traits.

**Features**:

- Allows implementing [`NdFrom`] and [`NdTryFrom`] at the same time.
- Allows implementing [`NdFromStr`] parsing with additional context or interpretation.

**Relations**:

- [`From`] **does** auto-implement [`TryFrom`]
- [`From`] **does** auto-implement [`NdFrom`]
- [`TryFrom`] **does** auto-implement [`NdTryFrom`]
- [`NdFrom`] **does not** auto-implement [`NdTryFrom`]
