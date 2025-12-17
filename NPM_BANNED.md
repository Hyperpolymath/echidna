# ⛔ NPM IS BANNED IN THIS PROJECT

## Policy

This project uses **Deno** as its JavaScript/TypeScript runtime. The following are **STRICTLY FORBIDDEN**:

- ❌ `npm install` / `npm i`
- ❌ `npx`
- ❌ `package-lock.json`
- ❌ `node_modules/`
- ❌ Bare imports like `import x from "lodash"`

## Approved Alternatives

### Package Management
```bash
# ✅ Use Deno tasks
deno task check
deno task lint
deno task daemon

# ✅ Use deno.json for dependencies
# Imports are specified in deno.json "imports" field
```

### Dependencies
```typescript
// ✅ CORRECT: Use https:// imports
import { serve } from "https://deno.land/std@0.224.0/http/server.ts";

// ✅ CORRECT: Use npm: specifier (Deno-native)
import z3 from "npm:z3-solver@4.12.4";

// ✅ CORRECT: Use esm.sh CDN
import React from "https://esm.sh/react@18.2.0";

// ❌ WRONG: Bare npm imports
import lodash from "lodash";  // BANNED
```

### Running Scripts
```bash
# ❌ BANNED
npm run dev
npm start
npx some-tool

# ✅ APPROVED
deno task dev
deno run --allow-net script.ts
```

## Why?

1. **Security**: Deno has better security defaults with explicit permissions
2. **Simplicity**: No node_modules, no package-lock.json conflicts
3. **Standards**: Uses web standards and ES modules natively
4. **Speed**: Faster startup, no npm install step
5. **Project Policy**: RSR (Rhodium Standard Repository) compliance

## Enforcement

- Pre-commit hooks block npm usage
- CI/CD fails on npm artifacts
- Code review rejects npm dependencies

## Exceptions

The only exception is the `src/rescript/` directory which requires ReScript compiler tooling. This is being migrated to Deno-compatible tooling.

## Need Help?

See the [Deno documentation](https://deno.land/manual) or ask in the project chat.
