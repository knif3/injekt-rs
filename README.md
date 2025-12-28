# Dependency Injection Container for Rust

A lightweight, thread-safe dependency injection container with async initialization and lazy resolution.

## Features

- **Thread-safe** - Built with `parking_lot::RwLock`
- **Async-first** - Native async service initialization
- **Lazy loading** - Defer resolution until first use
- **Type-safe** - Compile-time dependency checking
- **Zero unsafe code**

## Installation

```toml
[dependencies]
parking_lot = "0.12"
tokio = { version = "1", features = ["rt", "macros"] }
```

## Quick Start

```rust,ignore
use std::sync::Arc;

#[derive(Clone)]
struct Database { url: String }

#[derive(Clone)]
struct Cache { host: String }

// Build container
let injector = ContainerBuilder::new()
    .register(Database { url: "postgres://localhost".into() })
    .register(Cache { host: "redis://localhost".into() })
    .build_injector();

// Resolve services
let db: Arc<Database> = injector.resolve();
let cache: Arc<Cache> = injector.resolve();
```

## Core Patterns

### Injectable - Immediate Dependency Resolution

Use when all dependencies are needed at construction time. Resolve deps in `inject()`, perform async setup in `initialize()`.

```rust,ignore
struct UserService {
    db: Arc<Database>,
    cache: Arc<Cache>,
}

impl Injectable for UserService {
    type Output = ();
    type Error = Box<dyn std::error::Error>;

    fn inject(container: &Container) -> Self {
        Self {
            db: container.resolve(),
            cache: container.resolve(),
        }
    }

    async fn initialize(&self) -> Result<(), Self::Error> {
        self.db.connect().await?;
        Ok(())
    }
}

// Register and use
let injector = ContainerBuilder::new()
    .register(Database { url: "...".into() })
    .register(Cache { host: "...".into() })
    .register_injectable::<UserService>()
    .build_injector();

injector.create::<UserService>().await?;
```

### LazyInjectable - Dynamic Resolution

Use for plugin systems, circular dependencies, or when you need to resolve dependencies dynamically.

```rust,ignore
struct PluginManager {
    container: Arc<Container>,
    db: Lazy<Database>,
}

impl LazyInjectable for PluginManager {
    type Output = ();
    type Error = Box<dyn std::error::Error>;

    fn inject(container: Arc<Container>) -> Self {
        Self {
            db: container.resolve_lazy(),
            container,
        }
    }

    async fn initialize(&self) -> Result<(), Self::Error> {
        // Resolve dependencies as needed
        let config = self.container.resolve::<Config>();
        Ok(())
    }
}
```

### Lazy<T> - Deferred Resolution

Defer resolution of individual dependencies until they're actually used.

```rust,ignore
struct ReportGenerator {
    db: Lazy<Database>,
    cache: Lazy<Cache>,
}

impl ReportGenerator {
    fn quick_report(&self) -> Report {
        let cache = self.cache.get(); // db never resolved
        // ...
    }
}
```

## When to Use What

| Pattern | Use Case | Example |
|---------|----------|---------|
| **Injectable** | Dependencies needed immediately | Core services, repositories, API clients |
| **LazyInjectable** | Dynamic/deferred resolution | Plugins, background workers, circular deps |
| **Lazy<T>** | Specific dependency might not be used | Optional features, expensive resources |

**Rule of thumb:** Use `Injectable` for 90% of cases. Only use `LazyInjectable` when you genuinely need dynamic resolution.

## Registration Methods

```rust,ignore
ContainerBuilder::new()
    // Direct instance
    .register(Database { url: "...".into() })
    
    // Factory function
    .register_factory(|c| {
        let config = c.resolve::<Config>();
        Database::new(&config.db_url)
    })
    
    // Injectable trait
    .register_injectable::<UserService>()
    
    // LazyInjectable trait
    .register_lazy_injectable::<PluginManager>()
    
    .build_injector();
```

## Error Handling

```rust,ignore
// Panics if not found
let db: Arc<Database> = injector.resolve();

// Returns Result
match injector.try_resolve::<Database>() {
    Ok(db) => println!("Found"),
    Err(ResolutionError::NotRegistered { type_name }) => {
        eprintln!("Not found: {}", type_name)
    }
    Err(ResolutionError::TypeMismatch { type_name }) => {
        eprintln!("Type mismatch: {}", type_name)
    }
}
```

## Common Patterns

### Configuration

```rust,ignore
#[derive(Clone)]
struct AppConfig {
    db_url: String,
    api_key: String,
}

let config = AppConfig {
    db_url: std::env::var("DATABASE_URL").unwrap(),
    api_key: std::env::var("API_KEY").unwrap(),
};

let injector = ContainerBuilder::new()
    .register(config)
    .register_factory(|c| {
        let cfg = c.resolve::<AppConfig>();
        Database::new(&cfg.db_url)
    })
    .build_injector();
```

### Application Initializer

```rust,ignore
struct AppInitializer {
    db: Arc<Database>,
    cache: Arc<Cache>,
    queue: Arc<MessageQueue>,
}

impl Injectable for AppInitializer {
    type Output = ();
    type Error = Box<dyn std::error::Error>;

    fn inject(container: &Container) -> Self {
        Self {
            db: container.resolve(),
            cache: container.resolve(),
            queue: container.resolve(),
        }
    }

    async fn initialize(&self) -> Result<(), Self::Error> {
        self.db.connect().await?;
        self.cache.connect().await?;
        self.queue.start().await?;
        Ok(())
    }
}

// Single initialization point
injector.create::<AppInitializer>().await?;
```

## Testing

```rust,ignore
#[tokio::test]
async fn test_user_service() {
    let injector = ContainerBuilder::new()
        .register(Database { url: "test://db".into() })
        .register(Cache { host: "test://cache".into() })
        .register_injectable::<UserService>()
        .build_injector();
    
    let result = injector.create::<UserService>().await;
    assert!(result.is_ok());
}
```

## Container Utilities

```rust,ignore
container.contains::<Database>()  // Check if registered
container.len()                    // Number of services
container.is_empty()              // Check if empty
container.clear()                 // Clear all (testing)
```

## Best Practices

### Do
- Resolve all dependencies in `inject()`
- Use `initialize()` only for async setup
- Prefer `Injectable` for most cases
- Register services at startup
- Use `try_resolve()` when service might not exist

### Don't
- Resolve dependencies in `initialize()`
- Store `Container` in `Injectable` services
- Create circular dependencies
- Register services during request handling

## Performance

- **Resolution**: O(1) hash lookup with read lock
- **Memory**: Services stored as `Arc<T>` (cheap cloning)
- **Thread Safety**: Lock-free reads with `parking_lot::RwLock`
- **Lazy Init**: One-time initialization with `OnceLock`

## FAQ

**Q: Injectable vs LazyInjectable?**  
A: Use `Injectable` unless you need dynamic resolution.

**Q: Can I register after building?**  
A: Yes, but recommended to register at startup.

**Q: Handle circular dependencies?**  
A: Use `LazyInjectable` with `Lazy<T>`.

**Q: Production ready?**  
A: Well-tested and follows Rust best practices. Review for your use case.

**Q: Works with actix/axum/rocket?**  
A: Yes! Store `Injector` in app state.
