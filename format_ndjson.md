An exported `.ndjson` file will begin with an initial `meta` object which includes version info for the exporter and lean:

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
        } 
    }
}
```

followed by a sequence of primitives with integer tags (Name, Level, or Expr) and declartions (axiom, definition, theorem, opaque, quot, inductive, constructor, recursor). The construction of these elements is as follows:

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

ConstantInfo.axiomInfo
```
{
    "axiomInfo": {
        "name": integer,
        "levelParams": Array<integer>,
        "type": integer,
        "isUnsafe": boolean
    }
}
```

ConstantInfo.defnInfo
```
{
    "defnInfo": {
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


ConstantInfo.thmInfo
```
{
    "thmInfo": {
        "name": integer,
        "levelParams": Array<integer>,
        "type": integer,
        "value": integer,
        "all": Array<integer>
    }
}
```

ConstantInfo.opaqueInfo
```
{
    "opaqueInfo": {
        "name": integer,
        "levelParams": Array<integer>,
        "type": integer,
        "value": integer,
        "isUnsafe": boolean,
        "all": Array<integer>
    }
}
```

ConstantInfo.quotInfo
```
{
    "quotInfo": {
        "name": integer,
        "levelParams": Array<integer>,
        "type": integer,
        "kind": "type" | "ctor" | "lift" | "ind"
    }
}
```

ConstantInfo.inductInfo
```
{
    "inductInfo": {
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
}
```

ConstantInfo.ctorInfo
```
{
    "ctorInfo": {
        "name": integer,
        "levelParams": Array<integer>,
        "type": integer,
        "induct": integer,
        "cidx": integer,
        "numParams": integer,
        "numFields": integer,
        "isUnsafe": boolean
    }
}
```

RecursorRule:
```
{
    "RecursorRule": {
        "ctor": integer,
        "nfields": integer,
        "rhs": integer
    }
}
```

ConstantInfo.recInfo
```
{
    "recInfo": {
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
}
```