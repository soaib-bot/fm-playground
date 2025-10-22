import uuid
from datetime import datetime, timedelta
from typing import Dict, Optional


class LimbooleCache:
    """Represents a single string cache with TTL support."""

    def __init__(
        self, value: str, previous: str, current: str, ttl_seconds: int = 3600
    ):
        self.cache_id = str(uuid.uuid4())
        self.value = value
        self.previous = previous
        self.current = current
        self.created_at = datetime.now()
        self.last_accessed = datetime.now()
        self.ttl_seconds = ttl_seconds

    def is_expired(self) -> bool:
        """Check if cache has expired based on TTL."""
        expiry_time = self.last_accessed + timedelta(seconds=self.ttl_seconds)
        return datetime.now() > expiry_time

    def get_value(self) -> str:
        """Get the cached value and update last accessed time."""
        self.last_accessed = datetime.now()
        return self.value

    def get_previous(self) -> str:
        """Get the previous formula."""
        return self.previous

    def get_current(self) -> str:
        """Get the current formula."""
        return self.current

    def to_dict(self) -> dict:
        """Convert cache metadata to dict (without the actual value)."""
        return {
            "cache_id": self.cache_id,
            "created_at": self.created_at.isoformat(),
            "last_accessed": self.last_accessed.isoformat(),
            "ttl_seconds": self.ttl_seconds,
            "expires_at": (
                self.last_accessed + timedelta(seconds=self.ttl_seconds)
            ).isoformat(),
        }


class CacheManager:
    """Manages multiple string caches with automatic cleanup."""

    def __init__(self):
        self.caches: Dict[str, LimbooleCache] = {}

    def create_cache(
        self, value: str, previous: str, current: str, ttl_seconds: int = 3600
    ) -> str:
        """Create a new string cache and return its ID."""
        cache = LimbooleCache(value, previous, current, ttl_seconds)
        self.caches[cache.cache_id] = cache
        self._cleanup_expired()
        return cache.cache_id

    def get_value(self, cache_id: str) -> Optional[str]:
        """Get value from a cache."""
        cache = self.caches.get(cache_id)
        if not cache:
            return None

        if cache.is_expired():
            self.delete_cache(cache_id)
            return None

        return cache.get_value()

    def get_previous(self, cache_id: str) -> Optional[str]:
        """Get previous formula from a cache."""
        cache = self.caches.get(cache_id)
        if not cache:
            return None

        if cache.is_expired():
            self.delete_cache(cache_id)
            return None

        return cache.previous

    def get_current(self, cache_id: str) -> Optional[str]:
        """Get current formula from a cache."""
        cache = self.caches.get(cache_id)
        if not cache:
            return None

        if cache.is_expired():
            self.delete_cache(cache_id)
            return None

        return cache.current

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

    def update_cache(self, cache_id: str, new_value: str) -> bool:
        """Update the value of an existing cache."""
        cache = self.caches.get(cache_id)
        if cache and not cache.is_expired():
            cache.value = new_value
            cache.last_accessed = datetime.now()
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
cache_manager = CacheManager()
