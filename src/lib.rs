//! # Dependency Injection Container
//!
//! A lightweight, thread-safe dependency injection container for Rust with support for async
//! initialization, lazy resolution, and ergonomic service registration patterns.
//!
//! ## Features
//!
//! - **Thread-safe**: Built with `parking_lot::RwLock` for high-performance concurrent access
//! - **Type-safe**: Compile-time dependency checking with Rust's type system
//! - **Async-first**: Native support for async service initialization
//! - **Lazy loading**: Defer service resolution until first use with [`Lazy<T>`]
//! - **Injectable traits**: Declarative dependency patterns with [`Injectable`] and [`LazyInjectable`]
//! - **Fluent API**: Clean, chainable builder pattern for container setup
//! - **Zero unsafe code**: Pure safe Rust implementation
//!
//! ## Quick Start
//!
//! ```rust
//! use std::sync::Arc;
//!
//! #[derive(Clone)]
//! struct Database { url: String }
//!
//! #[derive(Clone)]
//! struct Cache { host: String }
//!
//! // Create and configure container
//! let injector = ContainerBuilder::new()
//!     .register(Database { url: "postgres://localhost".into() })
//!     .register(Cache { host: "redis://localhost".into() })
//!     .build_injector();
//!
//! // Resolve services
//! let db: Arc<Database> = injector.resolve();
//! let cache: Arc<Cache> = injector.resolve();
//! ```

use parking_lot::RwLock;
use std::any::{Any, TypeId};
use std::collections::HashMap;
use std::fmt;
use std::sync::{Arc, OnceLock};

// ============================================================================
// Core Traits
// ============================================================================

/// Trait for services with immediate dependency injection.
///
/// All dependencies are resolved synchronously in `inject()`, and `initialize()`
/// performs only async setup work (connections, warming caches, etc.).
///
/// # Example
///
/// ```rust
/// struct UserService {
///     db: Arc<Database>,
///     cache: Arc<Cache>,
/// }
///
/// impl Injectable for UserService {
///     type Output = ();
///     type Error = Box<dyn std::error::Error>;
///
///     fn inject(container: &Container) -> Self {
///         Self {
///             db: container.resolve(),
///             cache: container.resolve(),
///         }
///     }
///
///     async fn initialize(&self) -> Result<(), Self::Error> {
///         // Perform async initialization
///         self.db.connect().await?;
///         Ok(())
///     }
/// }
/// ```
pub trait Injectable: Send + Sync + 'static {
    /// The type returned by successful initialization
    type Output;
    /// The error type returned by failed initialization
    type Error;

    /// Creates a new instance by resolving dependencies from the container.
    ///
    /// All dependencies should be resolved here, not in `initialize()`.
    fn inject(container: &Container) -> Self
    where
        Self: Sized;

    /// Performs async initialization after dependencies have been injected.
    ///
    /// This should only contain async setup logic (connections, validations, etc.),
    /// not dependency resolution.
    fn initialize(&self) -> impl std::future::Future<Output = Result<Self::Output, Self::Error>> + Send;
}

/// Trait for services that need lazy or dynamic dependency resolution.
///
/// Use this when you need to break circular dependencies, defer expensive initialization,
/// or resolve dependencies dynamically at runtime (e.g., plugin systems).
///
/// # Example
///
/// ```rust
/// struct PluginManager {
///     container: Arc<Container>,
///     db: Lazy<Database>,
/// }
///
/// impl LazyInjectable for PluginManager {
///     type Output = ();
///     type Error = Box<dyn std::error::Error>;
///
///     fn inject(container: Arc<Container>) -> Self {
///         Self {
///             db: container.resolve_lazy(),
///             container,
///         }
///     }
///
///     async fn initialize(&self) -> Result<(), Self::Error> {
///         // Can resolve more dependencies dynamically
///         let config = self.container.resolve::<Config>();
///         Ok(())
///     }
/// }
/// ```
pub trait LazyInjectable: Send + Sync + 'static {
    /// The type returned by successful initialization
    type Output;
    /// The error type returned by failed initialization
    type Error;

    /// Creates a new instance with an owned reference to the container.
    fn inject(container: Arc<Container>) -> Self
    where
        Self: Sized;

    /// Performs async initialization after construction.
    ///
    /// Can use the stored container reference to resolve dependencies dynamically.
    fn initialize(&self) -> impl std::future::Future<Output = Result<Self::Output, Self::Error>> + Send;
}

// ============================================================================
// Error Types
// ============================================================================

/// Errors that can occur during service resolution.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ResolutionError {
    /// Service was not found in the container
    NotRegistered { type_name: &'static str },
    /// Service type mismatch during downcast
    TypeMismatch { type_name: &'static str },
}

impl fmt::Display for ResolutionError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NotRegistered { type_name } => {
                write!(f, "Service not registered: {}", type_name)
            }
            Self::TypeMismatch { type_name } => {
                write!(f, "Failed to downcast service: {}", type_name)
            }
        }
    }
}

impl std::error::Error for ResolutionError {}

// ============================================================================
// Lazy Wrapper
// ============================================================================

/// A wrapper that defers service resolution until first access.
///
/// Uses `OnceLock` internally for thread-safe, single initialization.
/// The service is resolved on the first call to [`get()`](Lazy::get).
///
/// # Example
///
/// ```rust
/// struct MyService {
///     db: Lazy<Database>,
/// }
///
/// impl MyService {
///     fn do_work(&self) {
///         let db = self.db.get(); // Resolves only once
///         // Use db...
///     }
/// }
/// ```
pub struct Lazy<T: Send + Sync + 'static> {
    container: Arc<Container>,
    value: OnceLock<Arc<T>>,
}

impl<T: Send + Sync + 'static> Lazy<T> {
    #[inline]
    const fn new(container: Arc<Container>) -> Self {
        Self {
            container,
            value: OnceLock::new(),
        }
    }

    /// Gets the service, resolving it from the container on first access.
    ///
    /// Thread-safe and will only resolve once, even under concurrent access.
    ///
    /// # Panics
    ///
    /// Panics if the service is not registered in the container.
    #[inline]
    pub fn get(&self) -> Arc<T> {
        self.value
            .get_or_init(|| self.container.resolve::<T>())
            .clone()
    }

    /// Tries to get the service with error handling.
    ///
    /// Returns `Err` if the service is not registered or cannot be downcast.
    pub fn try_get(&self) -> Result<Arc<T>, ResolutionError> {
        if let Some(v) = self.value.get() {
            return Ok(v.clone());
        }

        let resolved = self.container.try_resolve::<T>()?;
        // Try to store it, but ignore if another thread already did
        let _ = self.value.set(resolved.clone());
        Ok(resolved)
    }

    /// Checks if the lazy value has been initialized.
    #[inline]
    pub fn is_initialized(&self) -> bool {
        self.value.get().is_some()
    }
}

impl<T: Send + Sync + 'static> Clone for Lazy<T> {
    fn clone(&self) -> Self {
        Self {
            container: Arc::clone(&self.container),
            value: OnceLock::new(),
        }
    }
}

impl<T: Send + Sync + 'static> fmt::Debug for Lazy<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Lazy")
            .field("type", &std::any::type_name::<T>())
            .field("initialized", &self.is_initialized())
            .finish()
    }
}

// ============================================================================
// Container
// ============================================================================

/// The central registry that holds all service instances.
///
/// Thread-safe and can be safely shared across threads via `Arc<Container>`.
/// Services are stored as `Arc<T>`, making cloning cheap.
///
/// # Thread Safety
///
/// - Service resolution: Read locks (high concurrency)
/// - Service registration: Write locks (low concurrency, typically at startup)
pub struct Container {
    services: RwLock<HashMap<TypeId, Arc<dyn Any + Send + Sync>>>,
}

impl Container {
    /// Creates a new empty container.
    #[inline]
    pub fn new() -> Self {
        Self {
            services: RwLock::new(HashMap::new()),
        }
    }

    /// Registers a service using a factory function.
    ///
    /// The factory receives a reference to the container and can resolve dependencies.
    pub fn register<T, F>(&self, factory: F)
    where
        T: Send + Sync + 'static,
        F: FnOnce(&Container) -> T,
    {
        let instance = factory(self);
        self.services
            .write()
            .insert(TypeId::of::<T>(), Arc::new(instance));
    }

    /// Registers a service that needs `Arc<Container>` for lazy resolution.
    pub fn register_with_arc<T, F>(self: &Arc<Self>, factory: F)
    where
        T: Send + Sync + 'static,
        F: FnOnce(Arc<Container>) -> T,
    {
        let instance = factory(Arc::clone(self));
        self.services
            .write()
            .insert(TypeId::of::<T>(), Arc::new(instance));
    }

    /// Registers an [`Injectable`] service.
    #[inline]
    pub fn register_injectable<T>(&self)
    where
        T: Injectable,
    {
        self.register(T::inject);
    }

    /// Registers a [`LazyInjectable`] service.
    #[inline]
    pub fn register_lazy_injectable<T>(self: &Arc<Self>)
    where
        T: LazyInjectable,
    {
        self.register_with_arc(T::inject);
    }

    /// Resolves a service from the container.
    ///
    /// # Panics
    ///
    /// Panics if the service is not registered.
    #[inline]
    pub fn resolve<T: Send + Sync + 'static>(&self) -> Arc<T> {
        match self.try_resolve::<T>() {
            Ok(service) => service,
            Err(e) => panic!("{}", e),
        }
    }

    /// Tries to resolve a service, returning a `Result`.
    ///
    /// Use this when you want to handle missing services gracefully.
    pub fn try_resolve<T: Send + Sync + 'static>(&self) -> Result<Arc<T>, ResolutionError> {
        let type_id = TypeId::of::<T>();
        let services = self.services.read();

        let service = services
            .get(&type_id)
            .ok_or(ResolutionError::NotRegistered {
                type_name: std::any::type_name::<T>(),
            })?
            .clone();

        service
            .downcast::<T>()
            .map_err(|_| ResolutionError::TypeMismatch {
                type_name: std::any::type_name::<T>(),
            })
    }

    /// Creates a lazy resolver for a service.
    ///
    /// The service won't be resolved until [`Lazy::get()`] is called.
    #[inline]
    pub fn resolve_lazy<T: Send + Sync + 'static>(self: &Arc<Self>) -> Lazy<T> {
        Lazy::new(Arc::clone(self))
    }

    /// Checks if a service is registered.
    #[inline]
    pub fn contains<T: Send + Sync + 'static>(&self) -> bool {
        self.services.read().contains_key(&TypeId::of::<T>())
    }

    /// Returns the number of registered services.
    #[inline]
    pub fn len(&self) -> usize {
        self.services.read().len()
    }

    /// Checks if the container is empty.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.services.read().is_empty()
    }

    /// Clears all registered services.
    ///
    /// Useful for testing or when you need to rebuild the container.
    #[inline]
    pub fn clear(&self) {
        self.services.write().clear();
    }
}

impl Default for Container {
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

impl fmt::Debug for Container {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let services = self.services.read();
        f.debug_struct("Container")
            .field("service_count", &services.len())
            .finish_non_exhaustive()
    }
}

// ============================================================================
// Injector
// ============================================================================

/// High-level API for working with the dependency injection container.
///
/// Wraps a `Container` and provides convenient methods for creating
/// and initializing services.
pub struct Injector {
    container: Arc<Container>,
}

impl Injector {
    /// Creates a new injector from a container.
    #[inline]
    pub fn new(container: Container) -> Self {
        Self {
            container: Arc::new(container),
        }
    }

    /// Creates a new injector from an Arc-wrapped container.
    #[inline]
    pub fn from_arc(container: Arc<Container>) -> Self {
        Self { container }
    }

    /// Returns a reference to the underlying container.
    #[inline]
    pub fn container(&self) -> &Arc<Container> {
        &self.container
    }

    /// Creates and initializes an [`Injectable`] service.
    ///
    /// Calls `T::inject()` to create the service, then `initialize()` for async setup.
    pub async fn create<T>(&self) -> Result<T::Output, T::Error>
    where
        T: Injectable,
    {
        let service = T::inject(&self.container);
        service.initialize().await
    }

    /// Creates a [`LazyInjectable`] service without initializing it.
    ///
    /// Call `initialize()` manually when needed.
    #[inline]
    pub fn create_lazy<T>(&self) -> T
    where
        T: LazyInjectable,
    {
        T::inject(Arc::clone(&self.container))
    }

    /// Creates and initializes a [`LazyInjectable`] service.
    pub async fn create_lazy_initialized<T>(&self) -> Result<T::Output, T::Error>
    where
        T: LazyInjectable,
    {
        let service = T::inject(Arc::clone(&self.container));
        service.initialize().await
    }

    /// Resolves an already registered service.
    ///
    /// # Panics
    ///
    /// Panics if the service is not registered.
    #[inline]
    pub fn resolve<T: Send + Sync + 'static>(&self) -> Arc<T> {
        self.container.resolve()
    }

    /// Tries to resolve a service with error handling.
    #[inline]
    pub fn try_resolve<T: Send + Sync + 'static>(&self) -> Result<Arc<T>, ResolutionError> {
        self.container.try_resolve()
    }

    /// Checks if a service is registered.
    #[inline]
    pub fn contains<T: Send + Sync + 'static>(&self) -> bool {
        self.container.contains::<T>()
    }
}

impl fmt::Debug for Injector {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Injector")
            .field("container", &self.container)
            .finish()
    }
}

// ============================================================================
// Builder Pattern
// ============================================================================

/// Fluent builder for constructing a [`Container`].
///
/// Provides a chainable API for registering services.
pub struct ContainerBuilder {
    container: Arc<Container>,
}

impl ContainerBuilder {
    /// Creates a new builder with an empty container.
    #[inline]
    pub fn new() -> Self {
        Self {
            container: Arc::new(Container::new()),
        }
    }

    /// Registers a singleton instance.
    #[inline]
    pub fn register<T>(self, instance: T) -> Self
    where
        T: Send + Sync + 'static,
    {
        self.container.register(|_| instance);
        self
    }

    /// Registers a service using a factory function.
    #[inline]
    pub fn register_factory<T, F>(self, factory: F) -> Self
    where
        T: Send + Sync + 'static,
        F: FnOnce(&Container) -> T,
    {
        self.container.register(factory);
        self
    }

    /// Registers a service that needs `Arc<Container>` for lazy resolution.
    #[inline]
    pub fn register_with_container<T, F>(self, factory: F) -> Self
    where
        T: Send + Sync + 'static,
        F: FnOnce(Arc<Container>) -> T,
    {
        self.container.register_with_arc(factory);
        self
    }

    /// Registers an [`Injectable`] service.
    #[inline]
    pub fn register_injectable<T>(self) -> Self
    where
        T: Injectable,
    {
        self.container.register_injectable::<T>();
        self
    }

    /// Registers a [`LazyInjectable`] service.
    #[inline]
    pub fn register_lazy_injectable<T>(self) -> Self
    where
        T: LazyInjectable,
    {
        self.container.register_lazy_injectable::<T>();
        self
    }

    /// Builds and returns the raw container.
    ///
    /// For most cases, prefer [`build_injector()`](ContainerBuilder::build_injector).
    #[inline]
    pub fn build(self) -> Arc<Container> {
        self.container
    }

    /// Builds and returns an [`Injector`] wrapping the container.
    ///
    /// This is the recommended way to consume the builder.
    #[inline]
    pub fn build_injector(self) -> Injector {
        Injector::from_arc(self.container)
    }
}

impl Default for ContainerBuilder {
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Clone, Debug)]
    struct Database {
        url: String,
    }

    #[derive(Clone, Debug)]
    struct Cache {
        host: String,
    }

    struct UserService {
        db: Arc<Database>,
        cache: Arc<Cache>,
    }

    impl Injectable for UserService {
        type Output = bool;
        type Error = String;

        fn inject(container: &Container) -> Self {
            Self {
                db: container.resolve(),
                cache: container.resolve(),
            }
        }

        async fn initialize(&self) -> Result<bool, String> {
            Ok(true)
        }
    }

    struct EmailService {
        db: Lazy<Database>,
    }

    impl LazyInjectable for EmailService {
        type Output = bool;
        type Error = String;

        fn inject(container: Arc<Container>) -> Self {
            Self {
                db: container.resolve_lazy(),
            }
        }

        async fn initialize(&self) -> Result<bool, String> {
            let _db = self.db.get();
            Ok(true)
        }
    }

    #[tokio::test]
    async fn test_injectable_pattern() {
        let injector = ContainerBuilder::new()
            .register(Database {
                url: "postgres://localhost".to_string(),
            })
            .register(Cache {
                host: "redis://localhost".to_string(),
            })
            .register_injectable::<UserService>()
            .register_lazy_injectable::<EmailService>()
            .build_injector();

        let result = injector.create::<UserService>().await.unwrap();
        assert!(result);

        let email = injector.create_lazy::<EmailService>();
        let result = email.initialize().await.unwrap();
        assert!(result);
    }

    #[test]
    fn test_error_handling() {
        let container = Container::new();
        let result = container.try_resolve::<Database>();
        assert!(result.is_err());

        if let Err(ResolutionError::NotRegistered { type_name }) = result {
            assert!(type_name.contains("Database"));
        }
    }

    #[test]
    fn test_container_utilities() {
        let container = Container::new();
        assert!(container.is_empty());
        assert_eq!(container.len(), 0);

        container.register(|_| Database {
            url: "test".to_string(),
        });

        assert!(!container.is_empty());
        assert_eq!(container.len(), 1);
        assert!(container.contains::<Database>());
        assert!(!container.contains::<Cache>());

        container.clear();
        assert!(container.is_empty());
    }

    #[test]
    fn test_lazy_initialization() {
        let container = Arc::new(Container::new());
        container.register(|_| Database {
            url: "test".to_string(),
        });

        let lazy: Lazy<Database> = container.resolve_lazy();
        assert!(!lazy.is_initialized());

        let db = lazy.get();
        assert_eq!(db.url, "test");
        assert!(lazy.is_initialized());

        // Second call should return cached value
        let db2 = lazy.get();
        assert!(Arc::ptr_eq(&db, &db2));
    }

    #[test]
    fn test_concurrent_resolution() {
        use std::thread;

        let container = Arc::new(Container::new());
        container.register(|_| Database {
            url: "concurrent".to_string(),
        });

        let handles: Vec<_> = (0..10)
            .map(|_| {
                let container = Arc::clone(&container);
                thread::spawn(move || {
                    let db = container.resolve::<Database>();
                    db.url.clone()
                })
            })
            .collect();

        for handle in handles {
            let url = handle.join().unwrap();
            assert_eq!(url, "concurrent");
        }
    }

    #[test]
    fn test_resolution_error_types() {
        let container = Container::new();

        match container.try_resolve::<Database>() {
            Err(ResolutionError::NotRegistered { .. }) => (),
            _ => panic!("Expected NotRegistered error"),
        }
    }
}
