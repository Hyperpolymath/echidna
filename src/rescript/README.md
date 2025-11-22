# ECHIDNA ReScript UI

Production-ready web interface for the ECHIDNA Neurosymbolic Theorem Proving Platform.

## Overview

Modern, interactive proof assistant UI built with:
- **ReScript** - Type-safe functional programming (NOT JavaScript/TypeScript)
- **Deno** - Modern JavaScript runtime
- **React** - UI framework
- **Tailwind CSS** - Utility-first styling

## Features

### Core Components

1. **ProverSelector** - Choose from 12 theorem provers across 4 tiers
   - Tier 1 (6): Agda, Coq, Lean, Isabelle, Z3, CVC5
   - Tier 2 (3): Metamath, HOL Light, Mizar
   - Tier 3 (2): PVS, ACL2
   - Tier 4 (1): HOL4

2. **GoalList** - Display current proof goals
   - Hypotheses and context visualization
   - Current goal highlighting
   - Interactive goal selection

3. **TacticSuggester** - Neural tactic recommendations
   - AI-powered suggestions with confidence scores
   - Aspect tag filtering
   - One-click tactic application

4. **ProofViewer** - Proof state visualization
   - Real-time proof script display
   - Prover-specific syntax highlighting
   - Progress tracking

5. **TheoremSearch** - Search theorem libraries
   - OpenCyc ontology integration
   - Aspect-based filtering
   - Cross-prover search

6. **ProofTree** - Hierarchical proof structure
   - Interactive tree visualization
   - Node type indicators
   - Expandable/collapsible nodes

### Advanced Features

- **Real-time state management** - React hooks + reducers
- **API client** - Type-safe communication with Rust backend
- **Aspect tagging** - Semantic filtering system
- **Multi-prover support** - Unified interface for 12 provers
- **Responsive design** - Mobile and desktop optimized
- **Modern styling** - Tailwind CSS with custom themes

## Project Structure

```
src/rescript/
├── src/
│   ├── Main.res              # Application entry point
│   ├── state/
│   │   └── Store.res         # State management
│   ├── api/
│   │   └── Client.res        # Backend API client
│   └── components/
│       ├── ProverSelector.res
│       ├── GoalList.res
│       ├── TacticSuggester.res
│       ├── ProofViewer.res
│       ├── TheoremSearch.res
│       └── ProofTree.res
├── styles/
│   └── main.css              # Tailwind styles
├── package.json              # npm dependencies
├── rescript.json             # ReScript configuration
├── deno.json                 # Deno configuration
├── import_map.json           # Import mappings
├── tailwind.config.js        # Tailwind configuration
├── server.ts                 # Deno dev server
└── index.html                # Entry HTML

```

## Getting Started

### Prerequisites

- **Node.js** 18+ (for ReScript compiler and npm)
- **Deno** 1.37+ (for runtime and dev server)
- **Rust backend** running at `http://localhost:3000` (or set `ECHIDNA_API_URL`)

### Installation

```bash
# Install dependencies
cd src/rescript
npm install

# Or use Justfile from project root
just build-ui
```

### Development

```bash
# Start ReScript compiler in watch mode
npm run res:dev

# In another terminal, start Deno dev server
npm run dev

# Or use Justfile shortcuts
just watch-ui    # ReScript compiler
just dev-ui      # Deno dev server
```

The UI will be available at `http://localhost:8080`

### Building for Production

```bash
# Build ReScript → JavaScript
npm run res:build

# Bundle for production
npm run build

# Or use Justfile
just build-ui
```

### Serving

```bash
# Serve production build
npm run serve

# Or use Justfile
just serve-ui
```

## Configuration

### API Backend

Set the backend URL via environment variable:

```bash
export ECHIDNA_API_URL=http://localhost:3000
```

Or modify `server.ts`:

```typescript
const API_BACKEND = Deno.env.get("ECHIDNA_API_URL") || "http://localhost:3000";
```

### Tailwind CSS

Customize theme in `tailwind.config.js`:

```javascript
module.exports = {
  theme: {
    extend: {
      colors: {
        echidna: { /* custom colors */ }
      }
    }
  }
}
```

## API Integration

The UI communicates with the Rust backend via REST API:

- `POST /api/proof/init` - Initialize proof session
- `POST /api/proof/tactic` - Apply tactic
- `GET /api/proof/suggestions` - Get neural suggestions
- `POST /api/theorems/search` - Search theorems
- `GET /api/aspects/tags` - Get aspect tags
- `GET /api/proof/tree` - Get proof tree structure

See `src/api/Client.res` for complete API documentation.

## Development Workflow

### 1. Edit ReScript Files

Edit `.res` files in `src/` and `src/components/`. The compiler will:
- Type-check your code
- Generate `.bs.js` files (JavaScript output)
- Show errors in terminal

### 2. Hot Reload

The Deno dev server watches for changes and auto-reloads the browser.

### 3. Testing

```bash
# Run ReScript compiler checks
npm run check

# Or use Justfile
just build-ui
```

### 4. Code Style

ReScript enforces consistent formatting via the compiler. No need for Prettier/ESLint!

## Prover-Specific Features

Each prover has:
- Custom syntax highlighting
- Tier-based categorization
- Difficulty indicators
- Specific tactic suggestions

### Tier System

- **Tier 1**: Core provers (green) - Most common, best supported
- **Tier 2**: Extended (blue) - Additional coverage
- **Tier 3**: Specialized (yellow) - Domain-specific
- **Tier 4**: Advanced (orange) - Cutting-edge research

## State Management

The app uses a centralized reducer pattern:

```rescript
type state = {
  selectedProver: option<prover>,
  proofState: option<proofState>,
  tacticSuggestions: array<tacticSuggestion>,
  aspectTags: array<aspectTag>,
  // ...
}

type action =
  | SelectProver(prover)
  | UpdateProofState(proofState)
  | ApplyTactic(string)
  // ...
```

See `src/state/Store.res` for complete state management.

## Aspect Tagging

Aspect tags enable semantic filtering:

- **Domain**: algebra, geometry, logic, etc.
- **Difficulty**: basic, intermediate, advanced
- **Technique**: induction, contradiction, construction
- **Context**: research, teaching, verification

Tags integrate with OpenCyc ontology for intelligent theorem search.

## Performance

### Optimization Strategies

1. **Code splitting** - Lazy load components
2. **Memoization** - React.memo for expensive renders
3. **Virtual scrolling** - For large goal/theorem lists
4. **API caching** - Cache frequent queries
5. **WASM backend** - Optional Rust WASM integration

### Bundle Size

Production build targets:
- Initial load: <100KB (gzipped)
- Full app: <500KB (gzipped)

## Browser Support

- Chrome/Edge 90+
- Firefox 88+
- Safari 14+
- Mobile browsers (iOS Safari, Chrome Android)

## Troubleshooting

### ReScript Compilation Errors

```bash
# Clean build artifacts
npm run res:clean

# Rebuild
npm run res:build
```

### Deno Import Errors

Check `import_map.json` for correct module URLs. Deno caches imports in `~/.cache/deno`.

### API Connection Issues

1. Verify Rust backend is running: `curl http://localhost:3000/api/health`
2. Check CORS configuration in Rust backend
3. Verify `ECHIDNA_API_URL` environment variable

### Styling Issues

```bash
# Rebuild Tailwind CSS
npx tailwindcss -i ./styles/main.css -o ./dist/output.css
```

## Contributing

1. Write type-safe ReScript (no `external` unless necessary)
2. Use functional patterns (avoid mutation)
3. Add SPDX headers to all files
4. Follow RSR/CCCP compliance guidelines
5. Test across all 12 provers

## License

Dual-licensed:
- **MIT License**
- **Palimpsest License v0.6**

See project root for full license texts.

## Resources

- [ReScript Documentation](https://rescript-lang.org)
- [Deno Manual](https://deno.land/manual)
- [Tailwind CSS](https://tailwindcss.com)
- [ECHIDNA Main Docs](../../docs/)
- [Quill Repository](https://gitlab.com/non-initiate/rhodinised/quill)

## Support

For issues, questions, or contributions:
- Open an issue on GitLab
- Join the ECHIDNA development chat
- Read the main project CLAUDE.md

---

**Built with 🦔 by the ECHIDNA Project Team**
