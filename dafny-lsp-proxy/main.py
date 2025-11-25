import logging
import json
from typing import Optional
from fastapi import FastAPI, WebSocket, WebSocketDisconnect, HTTPException, Query
from fastapi.middleware.cors import CORSMiddleware
from dafny_lsp_proxy import DafnyLSPProxy

app = FastAPI(title="Dafny LSP Proxy API", version="2.0.0")

# Add CORS middleware
app.add_middleware(
    CORSMiddleware,
    allow_origins=["*"],
    allow_credentials=True,
    allow_methods=["*"],
    allow_headers=["*"],
)

# Global proxy instance
dafny_proxy = DafnyLSPProxy()


@app.on_event("startup")
async def startup_event():
    """Initialize the Dafny LSP proxy on startup"""
    try:
        await dafny_proxy.start_cleanup_task()
    except Exception as e:
        raise


@app.on_event("shutdown")
async def shutdown_event():
    """Clean up on shutdown"""
    await dafny_proxy.shutdown()


@app.get("/health")
async def health_check():
    """Health check endpoint"""
    return {
        "status": "healthy",
        "service": "dafny-lsp-proxy",
        "version": "2.0.0",
        "multi_user": True,
        "active_sessions": dafny_proxy.get_session_count(),
    }


@app.get("/sessions")
async def list_sessions():
    """List all active sessions"""
    return dafny_proxy.get_session_info()


@app.post("/sessions")
async def create_session():
    """Create a new session"""
    try:
        session = await dafny_proxy.create_session()
        return {"session_id": session.session_id, "status": "created"}
    except Exception as e:
        raise HTTPException(status_code=500, detail=str(e))


@app.delete("/sessions/{session_id}")
async def delete_session(session_id: str):
    """Delete a session"""
    session = await dafny_proxy.get_session(session_id)
    if not session:
        raise HTTPException(status_code=404, detail="Session not found")

    await dafny_proxy.remove_session(session_id)
    return {"status": "deleted", "session_id": session_id}


@app.websocket("/lsp")
async def websocket_endpoint(
    websocket: WebSocket, session_id: Optional[str] = Query(None)
):
    """
    WebSocket endpoint for LSP communication

    If session_id is provided, reuse existing session.
    Otherwise, create a new session automatically.
    """
    await websocket.accept()

    session = None
    auto_created = False

    try:
        # Get or create session
        if session_id:
            session = await dafny_proxy.get_session(session_id)
            if not session:
                error_msg = {
                    "jsonrpc": "2.0",
                    "error": {
                        "code": -32001,
                        "message": f"Session {session_id} not found",
                    },
                }
                await websocket.send_text(json.dumps(error_msg))
                await websocket.close()
                return
        else:
            # Auto-create session
            session = await dafny_proxy.create_session()
            session_id = session.session_id
            auto_created = True
            # Send session info to client
            session_info = {
                "jsonrpc": "2.0",
                "method": "session/created",
                "params": {"sessionId": session_id},
            }
            await websocket.send_text(json.dumps(session_info))

        # Attach websocket to session
        session.websocket = websocket

        # Handle messages
        while True:
            message = await websocket.receive_text()

            if not message.strip():
                continue

            try:
                parsed_message = json.loads(message)
                method = parsed_message.get("method", "unknown")
                msg_id = parsed_message.get("id", "notification")

                # Track initialization
                if method == "initialize":
                    session.initialized = True

                await session.send_to_lsp(parsed_message)

            except json.JSONDecodeError as e:
                await websocket.send_text(
                    json.dumps(
                        {
                            "jsonrpc": "2.0",
                            "error": {
                                "code": -32700,
                                "message": f"Parse error: {str(e)}",
                            },
                        }
                    )
                )
            except Exception as e:
                await websocket.send_text(
                    json.dumps(
                        {
                            "jsonrpc": "2.0",
                            "error": {
                                "code": -32603,
                                "message": f"Internal error: {str(e)}",
                            },
                        }
                    )
                )

    except WebSocketDisconnect:
        pass
    except Exception as e:
        pass
    finally:
        if session:
            session.websocket = None
            # If session was auto-created, remove it on disconnect
            if auto_created:
                await dafny_proxy.remove_session(session_id)
