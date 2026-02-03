# Lean 4 export format: version 3.1.0

An exported `.ndjson` file will begin with an initial `meta` object which includes version info for the exporter, lean, and export format:

Initial metadata object
```
{ 
    "meta": {
        "exporter": { 
            "name": string,
            "version": string 
            }, 
        "lean": { 
            "githash": string,
            "version": string 
        },
        "format": {
            "version": string
        } 
    }
}
```

followed by a sequence of primitives with integer tags (Name, Level, or Expr) and declartions (axiom, definition, theorem, opaque, quot, inductive, constructor, recursor), where related elements of an inductive or mutual inductive declaration (the inductive specifications, constructors, and recursors) are grouped together.

The export format contains information that is redundant and would likely be ignored or only validated by a full external checker (such as the types of recursors). These are included for the benefit of other tools that want all constants with their types (e.g. dependency analysis tools).

The construction of these elements is as described below (line breaks were added for readability; note that the NDJSON format requires these JSON objects to be rendered without any line breaks):

## Names

Name.str
```
{
    "str": {
        "pre": integer,
        "str": string
    },
    "in": integer,
}
```

Name.num
```
{
    "num": {
        "pre": integer,
        "i": integer
    }
    "in": integer,
}
```

## Levels

Level.succ
```
{
    "succ": integer
    "il": integer,
}
```

Level.max
```
{
    "max": [integer, integer],
    "il": integer,
}
```

Level.imax
```
{
    "imax": [integer, integer],
    "il": integer,
}

```

Level.param
```
{
    "param": integer,
    "il": integer,
}
```

## Expressions

Expr.bvar
```
{
  "bvar": integer,
  "ie": integer,
}
```


Expr.sort
```
{
    "sort": integer,
    "ie": integer,
}
```

Expr.const
```
{
    "const": {
        "name": integer,
        "us": Array<integer>
    }
    "ie": integer,
}
```

Expr.app
```
{
    "app": {
        "fn": number,
        "arg": number
    }
    "ie": integer,
}
```

Expr.lam
```
{
    "lam":  {
        "name": integer,
        "type": integer,
        "body": integer,
        "binderInfo": "default" | "implicit" | "strictImplicit" | "instImplicit"
    }
    "ie": integer,
}
```

Expr.forallE
```
{
    "forallE":  {
        "name": integer,
        "type": integer,
        "body": integer,
        "binderInfo": "default" | "implicit" | "strictImplicit" | "instImplicit"
    }
    "ie": integer,
}

```

Expr.letE
```
{
    "letE": {
        "name": integer,
        "type": integer,
        "value": integer,
        "body": integer,
        "nondep": boolean
    }
    "ie": integer,
}
```

Expr.proj
```
{
    "proj": {
        "typeName": integer,
        "idx": integer,
        "struct": integer
    }
    "ie": integer,
}
```
 
Expr.lit (Literal.natVal) 
```
{
    "natVal": string,
    "ie": integer
}
```

Expr.lit (Literal.strVal)
```
{
    "strVal": string,
    "ie": integer,
}
```

Expr.mdata
```
{
    "mdata": {
        "expr": integer,
        "data": object
    },
    "ie": integer
}
```

## Declarations

### Axiom

```
{
    "axiom": {
        "name": integer,
        "levelParams": Array<integer>,
        "type": integer,
        "isUnsafe": boolean
    }
}
```

### Definition
```
{
    "def": {
        "name": integer,
        "levelParams": Array<integer>,
        "type": integer,
        "value": integer,
        "hints": "opaque" | "abbrev" | {"regular": integer}
        "safety": "unsafe" | "safe" | "partial"
        "all": Array<integer>
    }
}
```

### Opaques
```
{
    "opaque": {
        "name": integer,
        "levelParams": Array<integer>,
        "type": integer,
        "value": integer,
        "isUnsafe": boolean,
        "all": Array<integer>
    }
}
```

### Theorems
```
{
    "thm": {
        "name": integer,
        "levelParams": Array<integer>,
        "type": integer,
        "value": integer,
        "all": Array<integer>
    }
}
```

### Quotients

NB: The official Lean kernel uses the field-less constructor `Lean.Declaration.quotDecl : Lean.Declaration` as the input to declare the quotient declarations, and then adds the four declarations that make up the quotient package to the environment. The export format includes the data of these generated declarations for convenience. 

```
{
    "quot": {
        "name": integer,
        "levelParams": Array<integer>,
        "type": integer,
        "kind": "type" | "ctor" | "lift" | "ind"
    }
}
```

### Inductive Declaration:

NB: The official Lean kernel expect a `Lean.Declaration.inductDecl`, which contains a (mutual) group of inductive declarations with their constructors. From that the kernel deries the recursors, and informational fields like `isRec`, `isReflexive` or `cidx`. The export format includes the data of these generated declarations for convenience. 


```
{
    "inductive": {
        "types": Array<InductiveVal>,
        "ctors": Array<ConstructorVal>,
        "recs": Array<RecursorVal>
    }
}
```

InductiveVal
```
{
    "name": integer,
    "levelParams": Array<integer>,
    "type": integer,
    "numParams": integer,
    "numIndices": integer,
    "all": Array<integer>,
    "ctors": Array<integer>,
    "numNested": integer,
    "isRec": boolean,
    "isUnsafe": boolean,
    "isReflexive": boolean,
}
```

ConstructorVal
```
{
    "name": integer,
    "levelParams": Array<integer>,
    "type": integer,
    "induct": integer,
    "cidx": integer,
    "numParams": integer,
    "numFields": integer,
    "isUnsafe": boolean
}
```

RecursorVal
```
{
    "name": integer,
    "levelParams": Array<integer>,
    "type": integer,
    "all": Array<integer>,
    "numParams": integer,
    "numIndices": integer,
    "numMotives": integer,
    "numMinors": integer,
    "rules": Array<RecursorRule>,
    "k": boolean,
    "isUnsafe": boolean
}
```

RecursorRule:
```
{
    "ctor": integer,
    "nfields": integer,
    "rhs": integer
}
```

