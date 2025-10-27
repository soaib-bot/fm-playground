import json

from db.db_query import update_metadata_by_permalink
from db.models import Code, Data, db


def test_update_metadata_by_permalink(app, db_session):
    """Test updating metadata by permalink."""
    with app.app_context():
        # Create test data in the database
        test_code = Code(code="test code")
        db_session.add(test_code)
        db_session.commit()

        # Create a Data entry with the permalink
        test_data = Data(
            permalink="limit-hefty-astute-spoils",
            check_type="test_check",
            code_id=test_code.id,
            meta=json.dumps({"original": "data"}),
        )
        db_session.add(test_data)
        db_session.commit()

        # Test data
        permalink = "limit-hefty-astute-spoils"
        new_metadata = {
            "redFound": [1, 2, 4],
        }

        result = update_metadata_by_permalink(permalink, new_metadata)
        assert result is True

        updated_data = db_session.query(Data).filter_by(permalink=permalink).first()
        assert updated_data is not None

        meta_dict = json.loads(updated_data.meta)
        assert meta_dict["redFound"] == [1, 2, 4]
