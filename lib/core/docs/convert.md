# Convert Extensions

**`Nd-kind` extensions for [`std::convert`]**

## Overview

The module defines `Nd-kind` conversion traits.

**Features**:

- Allows to implement [`NdFrom`] and [`NdTryFrom`] at the same time.
- Allows to implement [`NdFromStr`] parsing with additional context or interpretation.

**Relations**:

- [`From`] **does** auto-implement [`TryFrom`]
- [`From`] **does** auto-implement [`NdFrom`]
- [`TryFrom`] **does** auto-implement [`NdTryFrom`]
- [`NdFrom`] **does not** auto-implement [`NdTryFrom`]
