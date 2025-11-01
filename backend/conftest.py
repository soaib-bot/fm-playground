import sys
from pathlib import Path

import pytest

# Add the backend directory to the Python path
backend_dir = Path(__file__).parent
if str(backend_dir) not in sys.path:
    sys.path.insert(0, str(backend_dir))


@pytest.fixture(scope="function")
def app():
    """Create and configure a test Flask application instance."""
    from config import app as flask_app
    from config import db

    # Configure the app for testing
    flask_app.config["TESTING"] = True
    flask_app.config["SQLALCHEMY_DATABASE_URI"] = "sqlite:///:memory:"
    flask_app.config["SQLALCHEMY_TRACK_MODIFICATIONS"] = False

    # Create the database and tables
    with flask_app.app_context():
        db.create_all()
        yield flask_app
        db.session.remove()
        db.drop_all()


@pytest.fixture(scope="function")
def client(app):
    """Create a test client for the Flask application."""
    return app.test_client()


@pytest.fixture(scope="function")
def db_session(app):
    """Create a database session for testing."""
    from config import db

    with app.app_context():
        yield db.session
