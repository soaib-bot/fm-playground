# API Reference

This document provides detailed information about the FM Playground API endpoints, request/response formats, and usage examples based on the actual implementation.

## Base URLs

```
Backend API (Production): https://play.formal-methods.net/api
Backend API (Development): http://localhost:8000/api

Tool APIs (Development):
- Z3 API: http://localhost:8001
- Limboole API: http://localhost:8002  
- nuXmv API: http://localhost:8003
- Spectra API: http://localhost:8004
- Alloy API: http://localhost:8005
```

## Authentication

The FM Playground uses session-based authentication with OAuth2 providers.

### OAuth2 Authentication

#### Login Endpoints
```http
GET /api/login/google
GET /api/login/github
```
Redirects to OAuth provider for authentication.

#### OAuth Callback
```http
GET /api/auth/google
GET /api/auth/github
```
OAuth callback endpoints that process the authentication response.

### Session Management

#### Check Session Status
```http
GET /api/check_session
```

**Response (200 OK):**
```json
{
  "message": "Found user",
  "id": "google_123456789",
  "email": "user@example.com"
}
```

**Response (401 Unauthorized):**
```json
{
  "error": "401 Unauthorized"
}
```

#### Get Current User Profile
```http
GET /api/@me
```

**Response (200 OK):**
```json
{
  "message": "Found user",
  "id": "github_987654321",
  "email": "user@example.com"
}
```

#### Logout
```http
GET /api/logout
```

**Response (200 OK):**
```json
{
  "message": "Logged out successfully"
}
```

## Core Backend API Endpoints

### Specification Management

#### Save Specification
```http
POST /api/save
Content-Type: application/json

{
  "code": "string",           // The source Specification
  "check": "string",          // Tool type (SAT, SMT, XMV, SPECTRA, ALS)
  "parent": "string|null",    // Parent permalink for versioning
  "meta": "object|null"       // Additional metadata
}
```



#### Get Specification by Permalink
```http
GET /api/permalink/?p={permalink}
```

**Parameters:**
- `p` (required): The permalink identifier

**Response (200 OK):**
```json
{
  "code": "(assert (> x 0))\n(check-sat)"
}
```

**Response (404 Not Found):** Returns 404 if permalink doesn't exist.

### User History Management

#### Get User History
```http
GET /api/histories?page={page}
```

**Parameters:**
- `page` (optional): Page number (default: 1)

**Authentication:** Required

**Response (200 OK):**
```json
{
  "history": [
    {
      "id": 123,
      "permalink": "happy-bright-dog-moon",
      "check_type": "SMT",
      "time": "2024-01-15T10:30:00Z",
      "meta": null
    }
  ],
  "has_more_data": true
}
```

**Response (401 Unauthorized):**
```json
{
  "result": "fail",
  "message": "You are not logged in."
}
```

#### Unlink History Item
```http
PUT /api/unlink-history
Content-Type: application/json

{
  "id": 123
}
```

**Authentication:** Required

**Response (200 OK):**
```json
{
  "result": "success"
}
```

#### Get Specification by Data ID
```http
GET /api/code/{data_id}
```

**Authentication:** Required

**Response (200 OK):**
```json
{
  "result": "success",
  "code": "(assert (> x 0))",
  "check": "SMT",
  "permalink": "happy-bright-dog-moon"
}
```

#### Search User History
```http
GET /api/search?q={query}
```

**Parameters:**
- `q` (required): Search query

**Authentication:** Required

**Response (200 OK):**
```json
{
  "history": [
    {
      "id": 123,
      "permalink": "happy-bright-dog-moon",
      "check_type": "SMT",
      "time": "2024-01-15T10:30:00Z"
    }
  ],
  "has_more_data": false
}
```

#### Get History by Permalink
```http
GET /api/history/{permalink}
```

**Authentication:** Required

**Response (200 OK):**
```json
{
  "history": {
    "id": 123,
    "permalink": "happy-bright-dog-moon",
    "check_type": "SMT",
    "time": "2024-01-15T10:30:00Z",
    "meta": null
  }
}
```

### User Data Management

#### Download User Data
```http
GET /api/download-user-data
```

**Authentication:** Required

**Response (200 OK):**
```json
{
  "email": "user@example.com",
  "data": [
    {
      "id": 123,
      "permalink": "happy-bright-dog-moon",
      "code": "(assert (> x 0))",
      "check_type": "SMT",
      "time": "2024-01-15T10:30:00Z"
    }
  ]
}
```

#### Delete User Profile
```http
DELETE /api/delete-profile
```

**Authentication:** Required

**Response (200 OK):**
```json
{
  "result": "success"
}
```

### Metadata

#### Get Metadata
```http
GET /api/metadata?check={check_type}&p={permalink}
```

**Parameters:**
- `check` (required): Tool type (SAT, SMT, XMV, SPECTRA, ALS)
- `p` (required): Permalink identifier

**Response (200 OK):**
```json
{
  "permalink": "happy-bright-dog-moon",
  "check_type": "SMT",
  "created_at": "2024-01-15T10:30:00Z",
  "meta": null
}
```


API versioning follows semantic versioning principles with backward compatibility maintained.
