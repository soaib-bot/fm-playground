import uuid
from datetime import datetime, timedelta
from typing import Dict, Generator, Optional

from z3 import ModelRef


class GeneratorCache:
    """Represents a single generator cache with TTL support."""

    def __init__(self, generator: Generator, ttl_seconds: int = 3600):
        self.spec_id = str(uuid.uuid4())
        self.generator = generator
        self.created_at = datetime.now()
        self.last_accessed = datetime.now()
        self.ttl_seconds = ttl_seconds
        self.exhausted = False

    def is_expired(self) -> bool:
        """Check if cache has expired based on TTL."""
        expiry_time = self.last_accessed + timedelta(seconds=self.ttl_seconds)
        return datetime.now() > expiry_time

    def get_next(self) -> Optional[ModelRef]:
        """Get next item from generator."""
        self.last_accessed = datetime.now()
        try:
            return next(self.generator)
        except StopIteration:
            self.exhausted = True
            return None
        except Exception as e:
            # Catch any other exceptions from the generator
            print(f"Error getting next item from generator: {type(e).__name__}: {e}")
            self.exhausted = True
            return None

    def to_dict(self) -> dict:
        """Convert cache metadata to dict (without generator)."""
        return {
            "spec_id": self.spec_id,
            "created_at": self.created_at.isoformat(),
            "last_accessed": self.last_accessed.isoformat(),
            "ttl_seconds": self.ttl_seconds,
            "exhausted": self.exhausted,
            "expires_at": (
                self.last_accessed + timedelta(seconds=self.ttl_seconds)
            ).isoformat(),
        }


class GeneratorCacheManager:
    """Manages multiple generator caches with automatic cleanup."""

    def __init__(self):
        self.caches: Dict[str, GeneratorCache] = {}

    def create_cache(self, generator: Generator, ttl_seconds: int = 3600) -> str:
        """Create a new generator cache and return its ID."""
        cache = GeneratorCache(generator, ttl_seconds)
        self.caches[cache.spec_id] = cache
        self._cleanup_expired()
        return cache.spec_id

    def get_next(self, cache_id: str) -> Optional[ModelRef]:
        """Get next witness from a cache."""
        cache = self.caches.get(cache_id)
        if not cache:
            return None

        if cache.is_expired():
            self.delete_cache(cache_id)
            return None

        result = cache.get_next()

        # Clean up if exhausted
        if cache.exhausted:
            self.delete_cache(cache_id)

        return result

    def get_cache_info(self, cache_id: str) -> Optional[dict]:
        """Get cache metadata."""
        cache = self.caches.get(cache_id)
        if not cache:
            return None

        if cache.is_expired():
            self.delete_cache(cache_id)
            return None

        return cache.to_dict()

    def delete_cache(self, cache_id: str) -> bool:
        """Delete a cache."""
        if cache_id in self.caches:
            del self.caches[cache_id]
            return True
        return False

    def _cleanup_expired(self):
        """Remove expired caches."""
        expired_ids = [cid for cid, cache in self.caches.items() if cache.is_expired()]
        for cid in expired_ids:
            del self.caches[cid]

    def list_caches(self) -> list:
        """List all active caches."""
        self._cleanup_expired()
        return [cache.to_dict() for cache in self.caches.values()]


# Global cache manager instance
cache_manager = GeneratorCacheManager()
