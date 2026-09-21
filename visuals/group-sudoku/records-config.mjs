// Set the HTTPS API URL after the server is provisioned; never put credentials here.
export const RECORDS_API_URL=['localhost','127.0.0.1'].includes(location.hostname)?'http://127.0.0.1:8782':'';
